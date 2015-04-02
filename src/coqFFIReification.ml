open Names
open Term
open Tactics
open Tacticals
open Refiner
open Tacmach
open Entries
open Inductive
open Declarations
open Declare
open Topconstr
open Constrexpr
open Constrintern
open Nameops
open Nametab
open Inductiveops
open Util

open CoqFFIConstants
open CoqFFIState

let one = lazy (Constr.mkApp(Lazy.force SExpr.i,[|Lazy.force Positive.xH|]))

let find_instance env evd tclass ty =
  let tc = Constr.mkApp(tclass, [|ty|]) in
  let (evd,evar) = Evarutil.new_evar env evd tc in
  let evd = Typeclasses.resolve_typeclasses env evd in
  Evarutil.nf_evar evd (Evd.existential_value evd (destEvar evar))

let find_encodable_instance env evd ty =
  find_instance env evd (Lazy.force Encodable.t) ty

let export_tag i = mk_positive i

(** Builds an S-Expr from a list of terms representing S-Exprs *)
let export_list l =
  List.fold_right (fun e t ->
    Constr.mkApp(Lazy.force SExpr.b, [|e;t|])) l (Lazy.force one)

(** Build the S-Expr exporting ith argument of constructor of mind of type
Ck : forall params, T1, ... Tn in the following [env] :
params, T1, ... T(i-1) |- Ti (= [ty])
*)
let export_arg env nargs mind ninds nparams ty i =
  let evd = Evd.from_env env in
  let (t, params) = decompose_app (Reduction.whd_betadeltaiota env ty) in
  let arg = Constr.mkRel (nargs-i) in
  match kind_of_term t with
  | Ind ((mind',k),u) when MutInd.equal mind mind' ->
      Constr.mkApp(Constr.mkRel (nargs+1+ninds-k), [|arg|])
  | _ ->
     let inst = find_encodable_instance env evd ty in
     Constr.mkApp(inst,[|arg|])

(** Split [ctxt] in two parts: one for [nparams] parameters and one for the
remainder *)
let extract_params nparams ctxt =
  (* [smash_rel_context] expands let-ins which might be costly in some cases *)
  let ctxt = Termops.smash_rel_context ctxt in
  let (rem,params) = List.chop (List.length ctxt - nparams) ctxt in
  (params, rem)

(** Return B tag [export_arg arg1] ... [export_arg arg2] *)
let export_constructor env mind ninds nparams substparams i ty =
  let ctxt,t = decompose_prod_assum ty in
  let ctxt = snd (extract_params nparams ctxt) in
  let ctxt = Termops.substl_rel_context substparams ctxt in
  (* TODO: what about let-ins? *)
  let nargs = Context.rel_context_nhyps ctxt in
  let env = Environ.push_rel_context ctxt env in
  (* TODO: check that we have no dependent types here *)
  (* The environment in which we interpret the type of each argument has nargs
more binders than the original one, but doesn't have the types of previous
arguments in scope. Hence, the type number j must be lifted by nargs-j *)
  let args = List.mapi (fun j (_,odecl,ty) ->
    export_arg env nargs mind ninds nparams (Vars.lift (nargs-j) ty) j
    ) (List.rev ctxt)
  in
  let tag = Constr.mkApp(Lazy.force SExpr.i, [|export_tag (i+1)|]) in
  let br = Constr.mkApp(Lazy.force SExpr.b, [|tag; export_list args|]) in
  let t = Termops.it_mkLambda_or_LetIn br ctxt in
  Pp.ppnl (Termops.print_constr t);
  t

let apply_params substparams t =
  let params = List.rev substparams in
  Constr.mkApp(t, Array.of_list params)

(** Generate the export function for the given inductive *)
(*
    fun x : ind =>
      match x return SExpr.t with
      | C0 => B [export 0] I
      | ...
      | Cn => B [export n] I
      end.
 *)
let export_inductive env ((mind,i as ind),u as pind) ninds nparams substparams oib =
  let ci = make_case_info env ind RegularStyle in
  let typs = arities_of_constructors env pind in
  (** We lift by 1 because the export function introduces a lambda. *)
  let ty = apply_params substparams (Constr.mkInd ind) in
  let env = Environ.push_rel (Anonymous,None,ty) env in
  let substparams = List.map (Vars.lift 1) substparams in
  let p = Constr.mkLambda(Anonymous, Vars.lift 1 ty, Lazy.force SExpr.t) in
  let c = Constr.mkRel 1 in
  let ac = Array.mapi (export_constructor env mind ninds nparams substparams) typs in
  let case = Constr.mkCase(ci,p,c,ac) in
  Constr.mkLambda(Anonymous, ty, case)

let type_of_export ty =
  Constr.mkApp(Lazy.force Encodable.t, [|ty|])

let type_of_export_fix ty =
  Constr.mkProd(Anonymous,ty, Lazy.force SExpr.t)

let type_of_import ty =
  Constr.mkApp(Lazy.force Decodable.t, [|ty|])

(** Build a substitution for parameters of [mib] and adds a quantification over
Reifiable.t instances for products in a sort *)
let gen_params mib tclass =
  let ctxt = mib.mind_params_ctxt in
  let nparamsrec = mib.mind_nparams_rec in
  let ctxt = fst (extract_params nparamsrec ctxt) in
  let (_,subst,l) =
    (* From newer to older declarations *)
    Context.fold_rel_context_reverse (fun (n,substparams,l) (_,copt,ty) ->
      match copt with
      | None ->
	 let (l, n) =
	   if isSort ty then
	     ((Anonymous, Constr.mkApp(tclass, [|Constr.mkRel 1|])) :: l, n + 2)
	   else (l, n + 1)
	 in
	 let l = (Anonymous, ty) :: l in
	 let substparams = Constr.mkRel n :: substparams in
	 (n,substparams,l)
      | _ -> assert false
    ) ~init:(0,[],[]) ctxt 
  in
  List.rev subst, List.rev l

(* For an inductive ind with n mutual bodies *)
(* fix ind_export_1 := [export_inductive 1]

with ...

with ind_export_n := [export_inductive n]

 *)
let export_mind env ((mind,i as ind),u as pind) =
  let (mib,_) = lookup_mind_specif env ind in
  let n = Array.length mib.mind_packets in
  let recindexes = Array.make n 0 in
  let funnames = Array.make n Anonymous in
  let nparams = mib.mind_nparams_rec in
  let substparams, lams = gen_params mib (Lazy.force Encodable.t) in
  let env = Termops.push_rels_assum lams env in
  let export_ty = apply_params substparams (Constr.mkInd (mind,i)) in
  let typs =
    Array.init n (fun j ->
		  let ty = apply_params substparams (Constr.mkInd (mind,j)) in
		  type_of_export_fix ty)
  in
  let typs_assum = List.map (fun t -> (Anonymous,t)) (Array.to_list typs) in
  (* TODO: package env and substparams? *)
  let env = Termops.push_rels_assum typs_assum env in
  let substparams = List.map (Vars.lift n) substparams in
  let bodies =
    Array.mapi (fun i -> export_inductive env ((mind,i),u) n nparams substparams) mib.mind_packets
  in
  let t = Constr.mkFix((recindexes,i),(funnames,typs,bodies)) in
  let t = Constr.mkCast(t, DEFAULTcast, type_of_export export_ty) in
  Termops.it_mkLambda t lams


(* TODO *)
let import_mind env (mind,i as ind) =
  let (mib,_) = lookup_mind_specif env ind in
  let nparams = mib.mind_nparams_rec in
  let substparams, lams = gen_params mib (Lazy.force Decodable.t) in
  let import_ty = apply_params substparams (Constr.mkInd ind) in
  (* Lift corresponding to the argument (i.e. the s-expr) *)
  let ty = Vars.lift 1 import_ty in
  let none = Constr.mkApp(Lazy.force Init.none, [|ty|]) in
  let t = Constr.mkLambda(Anonymous, Lazy.force SExpr.t, none) in
  let t = Constr.mkCast(t, DEFAULTcast, type_of_import import_ty) in
  Termops.it_mkLambda t lams
