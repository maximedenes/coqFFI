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

let find_decodable_instance env evd ty =
  find_instance env evd (Lazy.force Decodable.t) ty

let export_tag i = mk_positive i

(** Builds an S-Expr from a list of terms representing S-Exprs *)
let export_list l =
  List.fold_right (fun e t ->
    Constr.mkApp(Lazy.force SExpr.b, [|e;t|])) l (Lazy.force one)

(** Build the S-Expr exporting ith argument of constructor of mind of type
Ck : forall params, T1, ... Tn in the following [env] :
params, T1, ... T(i-1) |- Ti (= [ty])
*)
let export_arg env nargs mind ninds ty i =
  let evd = Evd.from_env env in
  let (t, params) = decompose_app (Reduction.whd_betadeltaiota env ty) in
  let arg = Constr.mkRel (nargs-i) in
  match kind_of_term t with
  | Ind ((mind',k),u) when MutInd.equal mind mind' ->
     (* TODO: handle with type classes, like other cases *)
     (* May require to remove the cast and type fixpoints with the type class *)
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
    export_arg env nargs mind ninds (Vars.lift (nargs-j) ty) j
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

(* For non-constant constructors: *)
(* match Rel 1 with
| I => None
| B a1 args => match decode a1 with
               | Some v1 =>

match Rel 1 with ...
              ... B an _ => C v1 ... vn
 *)
let mk_case_sexpr env c ty case_I case_B =
  let (sexpr_ind,_) = destInd (Lazy.force SExpr.t) in
  let ci = make_case_info env sexpr_ind RegularStyle in
  let ty = Constr.mkApp(Lazy.force Init.option, [|ty|]) in
  let ty = Vars.lift 1 ty in
  let p = Constr.mkLambda(Anonymous, Lazy.force SExpr.t, ty) in
  let case_I = Constr.mkLambda(Anonymous, Lazy.force Positive.t, case_I) in
  let case_B = Constr.mkLambda(Anonymous, Lazy.force SExpr.t, case_B) in
  let case_B = Constr.mkLambda(Anonymous, Lazy.force SExpr.t, case_B) in
  Constr.mkCase(ci,p,c,[|case_I;case_B|])

let mk_case_positive env c ty case_xI case_xO case_xH =
  let (positive_ind,_) = destInd (Lazy.force Positive.t) in
  let ci = make_case_info env positive_ind RegularStyle in
  let ty = Constr.mkApp(Lazy.force Init.option, [|ty|]) in
  let ty = Vars.lift 1 ty in
  let p = Constr.mkLambda(Anonymous, Lazy.force Positive.t, ty) in
  let case_xI = Constr.mkLambda(Anonymous, Lazy.force Positive.t, case_xI) in
  let case_xO = Constr.mkLambda(Anonymous, Lazy.force Positive.t, case_xO) in
  Constr.mkCase(ci,p,c,[|case_xI;case_xO;case_xH|])

let mk_case_option env c ty ret_ty case_Some case_None =
  let (positive_ind,_) = destInd (Lazy.force Init.option) in
  let ci = make_case_info env positive_ind RegularStyle in
  let ret_ty = Constr.mkApp(Lazy.force Init.option, [|ret_ty|]) in
  let ret_ty = Vars.lift 1 ret_ty in
  let oty = Constr.mkApp(Lazy.force Init.option, [|ty|]) in
  let p = Constr.mkLambda(Anonymous,oty, ret_ty) in
  let case_Some = Constr.mkLambda(Anonymous, ty, case_Some) in
  Constr.mkCase(ci,p,c,[|case_Some;case_None|])

let rec import_args env sargs ret_ty c cargs ctxt =
  match ctxt with
  | [] ->
     let c = Constr.mkApp(c, Array.of_list (List.rev cargs)) in
     Constr.mkApp(Lazy.force Init.some, [|ret_ty;c|])
  | (_, None, ty) :: ctxt' ->
     let evd = Evd.from_env env in
     (* sargs encodes the list of arguments, let's pattern match on it *)
     let match_sargs match_arg =
       let none = Constr.mkApp(Lazy.force Init.none, [|ret_ty|]) in
       let case_I = Vars.lift 1 none in
       mk_case_sexpr env sargs ret_ty case_I match_arg
     in
     let env = Environ.push_rel (Anonymous, None, Lazy.force SExpr.t) env in
     let env = Environ.push_rel (Anonymous, None, Lazy.force SExpr.t) env in
     (* now we need to decode the argument *)
     (* let ty = Vars.lift 2 ty in *)
     let ret_ty = Vars.lift 2 ret_ty in
     let inst = find_decodable_instance env evd ty in
     let arg = Constr.mkApp(inst,[|Constr.mkRel 2|]) in
     let case_None = Constr.mkApp(Lazy.force Init.none, [|ret_ty|]) in
     let carg = Constr.mkRel 1 in
     let sargs = Constr.mkRel 2 in
     let env' = Environ.push_rel (Anonymous, None, ty) env in
     let c = Vars.lift 3 c in
     let cargs = List.map (Vars.lift 3) cargs in
     (* We should lift by 3 but each item in ctxt already has in scope its predecessors *)
  let ctxt' = List.rev ctxt' in
     let ctxt' = Termops.lift_rel_context 2 ctxt' in
  let ctxt' = List.rev ctxt' in
     let ret_ty' = Vars.lift 1 ret_ty in
     let case_Some = import_args env' sargs ret_ty' c (carg :: cargs) ctxt' in
     match_sargs (mk_case_option env arg ty ret_ty case_Some case_None)
  | _ -> assert false

let import_args env sarg ret_ty c ctxt =
  let ctxt = List.rev ctxt in
  let ctxt = Termops.lift_rel_context 2 ctxt in
  let ctxt = List.rev ctxt in
  import_args env sarg ret_ty c [] ctxt

let import_constructor env sargs pind ninds nparams substparams i ty =
  let constr_ty = (arities_of_constructors env pind).(i) in
  let ctxt,t = decompose_prod_assum constr_ty in
  let ctxt = snd (extract_params nparams ctxt) in
  let ctxt = Termops.substl_rel_context substparams ctxt in
  Pp.ppnl (Termops.print_env env);
  print_endline "Constructor context:";
  let ctxt = List.rev ctxt in
  List.iter (fun c -> Pp.ppnl (Termops.pr_rel_decl env c)) ctxt;
  (*  List.iter (fun c -> Pp.ppnl (Termops.print_constr c)) substparams; *)
  (* TODO: what about let-ins? *)
  let c = Constr.mkConstruct (fst pind,(i+1)) in
  let c = apply_params substparams c in
  import_args env sargs ty c ctxt

let rec import_tag env c ty sargs max_tag n current_tag ind ninds nparams substparams =
  let new_tag = (1 lsl n) + current_tag in
  if new_tag > max_tag then
    Constr.mkApp(Lazy.force Init.none, [|ty|])
  else
  let case_xH = import_constructor env sargs ind ninds nparams substparams (new_tag-1) ty in
  let c = Constr.mkRel 1 in
  let ty' = Vars.lift 1 ty in
  let sargs = Vars.lift 1 sargs in
  let substparams = List.map (Vars.lift 1) substparams in
  let env' = Environ.push_rel (Anonymous, None, Lazy.force Positive.t) env in
  let case_xO = import_tag env' c ty' sargs max_tag (n+1) current_tag ind ninds nparams substparams in
  let case_xI = import_tag env' c ty' sargs max_tag (n+1) new_tag ind ninds nparams substparams in
  mk_case_positive env c ty case_xI case_xO case_xH

let import_tag env c ty max_tag ind ninds nparams substparams =
  import_tag env c ty (Constr.mkRel 2) max_tag 0 0 ind ninds nparams substparams

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
  let ty = apply_params substparams (Constr.mkInd ind) in
  let env = Environ.push_rel (Anonymous, None, ty) env in
  (** We lift by 1 because the export function introduces a lambda. *)
  let substparams = List.map (Vars.lift 1) substparams in
  let p = Constr.mkLambda(Anonymous, Vars.lift 1 ty, Lazy.force SExpr.t) in
  let c = Constr.mkRel 1 in
  let ac = Array.mapi (export_constructor env mind ninds nparams substparams) typs in
  let case = Constr.mkCase(ci,p,c,ac) in
  Constr.mkLambda(Anonymous, ty, case)

let import_inductive env (ind,u as pind) ninds nparams substparams oib =
  let (sexpr_ind,_) = destInd (Lazy.force SExpr.t) in
  let ci = make_case_info env sexpr_ind RegularStyle in
  let typs = arities_of_constructors env pind in
  let ty = apply_params substparams (Constr.mkInd ind) in
  let ty = Vars.lift 1 ty in
  let env = Environ.push_rel (Anonymous, None, Lazy.force SExpr.t) env in
  (** First, a match on the S-Expr to split out the tag and arguments *)
  let match_sexpr match_tag =
    let c = Constr.mkRel 1 in
    let none = Constr.mkApp(Lazy.force Init.none, [|ty|]) in
    let case_I = Vars.lift 1 none in
    mk_case_sexpr env c ty case_I match_tag
  in
  (** Now we match on the tag *)
  let ty = Vars.lift 2 ty in
  let env = Environ.push_rel (Anonymous, None, Lazy.force SExpr.t) env in
  let env = Environ.push_rel (Anonymous, None, Lazy.force SExpr.t) env in
  let c = Constr.mkRel 2 (* First argument of B e1 e2 *) in
  let none = Constr.mkApp(Lazy.force Init.none, [|ty|]) in
  let case_B = Vars.lift 2 none in
  let max_tag = Array.length typs in
  (** We lift by 4:
      + 1 for the lambda introduced by the import function.
      + 2 for the first match (B e1 e2 case)
      + 1 for the second match (I tag case) *)
  let substparams = List.map (Vars.lift 4) substparams in
  let ty' = Vars.lift 1 ty in
  let env' = Environ.push_rel (Anonymous, None, Lazy.force Positive.t) env in
  let case_I = import_tag env' c ty' max_tag pind ninds nparams substparams in
  let case = match_sexpr (mk_case_sexpr env c ty case_I case_B) in
  Constr.mkLambda(Anonymous, Lazy.force SExpr.t, case)

let type_of_export ty =
  Constr.mkApp(Lazy.force Encodable.t, [|ty|])

let type_of_export_fix ty =
  Constr.mkProd(Anonymous, ty, Lazy.force SExpr.t)

let type_of_import ty =
  Constr.mkApp(Lazy.force Decodable.t, [|ty|])

let type_of_import_fix ty =
  let ty = Constr.mkApp(Lazy.force Init.option, [|ty|]) in
  Constr.mkProd(Anonymous, Lazy.force SExpr.t, Vars.lift 1 ty)

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
let codec_mind env tclass type_of type_of_fix codec_inductive
  ((mind,i as ind),u as pind) =
  let (mib,_) = lookup_mind_specif env ind in
  let n = Array.length mib.mind_packets in
  let recindexes = Array.make n 0 in
  let funnames = Array.make n Anonymous in
  let nparams = mib.mind_nparams_rec in
  let substparams, lams = gen_params mib tclass in
  let env = Termops.push_rels_assum lams env in
  let def_ty = apply_params substparams (Constr.mkInd (mind,i)) in
  let typs =
    Array.init n (fun j ->
		  let ty = apply_params substparams (Constr.mkInd (mind,j)) in
		  type_of_fix ty)
  in
  let typs_assum = List.map (fun t -> (Anonymous,t)) (Array.to_list typs) in
  (* TODO: package env and substparams? *)
  let env = Termops.push_rels_assum typs_assum env in
  let substparams = List.map (Vars.lift n) substparams in
  let bodies =
    Array.mapi (fun i -> codec_inductive env ((mind,i),u) n nparams substparams) mib.mind_packets
  in
  let t = Constr.mkFix((recindexes,i),(funnames,typs,bodies)) in
  let t = Constr.mkCast(t, DEFAULTcast, type_of def_ty) in
  Termops.it_mkLambda t lams

let encode_mind env pind =
  let tclass = Lazy.force Encodable.t in
  codec_mind env tclass type_of_export type_of_export_fix export_inductive pind

let decode_mind env pind =
  let tclass = Lazy.force Decodable.t in
  codec_mind env tclass type_of_import type_of_import_fix import_inductive pind
