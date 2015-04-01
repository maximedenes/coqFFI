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

let find_reifiable_instance env evd ty =
  (* let ctxt = Environ.empty_named_context_val in
  let (evd,ev) = Evarutil.new_pure_evar ctxt evd ty in *)
  let tc = Constr.mkApp(Lazy.force Reifiable.t, [|ty|]) in
  let (evd,evar) = Evarutil.new_evar env evd (* ~principal:true *) tc in
  (*  let tc = Termops.it_mkProd tc prods in *)
  let evd = Typeclasses.resolve_typeclasses env evd in
  Evarutil.nf_evar evd (Evd.existential_value evd (destEvar evar))

let rec export_tag i =
  if i > 1 then
    let digit =
      if i land 1 = 0 then Lazy.force Positive.xO
      else Lazy.force Positive.xI
    in
    Constr.mkApp(digit, [|export_tag (i lsr 1)|])
  else Lazy.force Positive.xH

(** Builds an S-Expr from a list of terms representing S-Exprs *)
let export_list l =
  List.fold_right (fun e t ->
    Constr.mkApp(Lazy.force SExpr.b, [|e;t|])) l (Lazy.force one)

(** Build the S-Expr exporting ith argument of constructor of mind of type
Ck : forall params, T1, ... Tn in the following [env] :
params, T1, ... T(i-1) |- Ti (= [ty])
*)
let export_arg env nargs mind ninds nparams substparams ty i =
  let evd = Evd.from_env env in
  let (t, params) = decompose_app (Reduction.whd_betadeltaiota env ty) in
  let arg = Constr.mkRel (nargs+1-i) in
  match kind_of_term t with
  | Ind ((mind',k),u) ->
    if MutInd.equal mind mind' then
      Constr.mkApp(Constr.mkRel (nargs+nparams+1+ninds-k), [|arg|])
    else
      (Printf.printf "mind=%s mind'=%s\n" (MutInd.to_string mind) (MutInd.to_string mind');
       let rels = Termops.free_rels ty in
       (* We rely here on the order underlying Int.Set.t *)
       let rels = Int.Set.elements rels in
       let nrels = List.length rels in
(*       let (evd,ty) =
	 List.fold_left (fun (evd,subst) r -> 
			 let (_,_,t) = Environ.lookup_rel r env in
			 let (evd,c) = Evarutil.new_evar (Global.env ()) evd t in
			 (evd, Vars.substnl [c] (r-1) ty)) (evd,ty) rels
       in*)
       (*
       let ty = Vars.substl (List.rev (Termops.rel_list 0 nrels)) ty in
	*)
(*       let ty =
	 List.fold_left (fun ty r -> 
			 let (_,_,t) = Environ.lookup_rel r env in
			 Constr.mkProd(Anonymous,t,ty)) ty rels
       in *)
(*
       let prods =
	 List.map (fun r -> 
		   let (_,_,ty) = Environ.lookup_rel r env in
		   (Anonymous,ty)) rels
       in
 *)
       (*       let ty = Vars.substl (List.rev subst) ty in *)
       let inst = find_reifiable_instance env evd ty in
       let ty = Vars.lift (nargs+1-i) ty in
       let inst = Vars.lift (nargs+1-i) inst in
       Constr.mkApp(Lazy.force Reifiable.export, [|ty;inst;arg|]))
  | Rel k ->
     (* The current context is forall params, forall arg0 ... forall arg(i-1) |- *)
     (* So we found parameter number (nparams - k + i - 1) *)
     let t = Vars.lift (nargs+nparams+ninds+1) substparams.(nparams - k + i - 1) in
     Constr.mkApp(t, Array.of_list (params @ [arg]))
  | _ ->
     let inst = find_reifiable_instance env evd ty in
     let ty = Vars.lift (nargs+1-i) ty in
     let inst = Vars.lift (nargs+1-i) inst in
     Constr.mkApp(Lazy.force Reifiable.export, [|ty;inst;arg|])

let rel_of_param nparams n =
  Constr.mkRel (2 * (nparams - n))

let rel_of_reifiable nparams n =
  Constr.mkRel (2 * (nparams - n) - 1)

(** Return B tag [export_arg arg1] ... [export_arg arg2] *)
let export_constructor env mind ninds nparams substparams i ty =
  let ctxt,t = decompose_prod_assum ty in
  (* [smash_rel_context] expands let-ins which might be costly in some cases *)
  let ctxt = Termops.smash_rel_context ctxt in
  let (ctxt,params) = List.chop (List.length ctxt - nparams) ctxt in
  let env = Environ.push_rel_context params env in
  let nargs = Context.rel_context_nhyps ctxt in
  let (env,args,_) = Context.fold_rel_context (fun (_,odecl,ty as decl) (env,args,i) ->
    match odecl with
    | None ->
       let arg = export_arg env nargs mind ninds nparams substparams ty i in
       let env = Environ.push_rel decl env in
       (env, arg :: args, i+1)
    | Some _ -> assert false)
    ctxt ~init:(env,[],1)
  in
  let tag = Constr.mkApp(Lazy.force SExpr.i, [|export_tag (i+1)|]) in
  let br = Constr.mkApp(Lazy.force SExpr.b, [|tag; export_list (List.rev args)|]) in
  let t = Termops.it_mkLambda_or_LetIn br ctxt in
  let relparams = List.init nparams (fun i -> Vars.lift (ninds+1) (rel_of_param nparams i)) in
  let t = Vars.substl (List.rev relparams) t in
  Pp.ppnl (Termops.print_constr t);
  t

let type_of_export_arg ninds nparams ty =
  let params = Array.init nparams (fun i -> Vars.lift ninds (rel_of_param nparams i)) in
  Constr.mkApp(ty,params)

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
  let ty = type_of_export_arg ninds nparams (Constr.mkInd ind) in
  let p = Constr.mkLambda(Anonymous, Vars.lift 1 ty, Lazy.force SExpr.t) in
  let c = Constr.mkRel 1 in
  let ac = Array.mapi (export_constructor env mind ninds nparams substparams) typs in
  let case = Constr.mkCase(ci,p,c,ac) in
  Constr.mkLambda(Anonymous, ty, case)

let apply_params nparams t =
  let params = Array.init nparams (rel_of_param nparams) in
  Constr.mkApp(t,params)

let apply_reifiables nparams t =
  let nargs = 2 * nparams in
  let args = Array.init nargs (fun i -> Constr.mkRel (nargs - i)) in
  Constr.mkApp(t,args)

let type_of_export nparams ty =
  let ty = apply_params nparams ty in
  Constr.mkProd(Anonymous,ty,Lazy.force SExpr.t)

let gen_params oproj mib =
  let ctxt = mib.mind_params_ctxt in
  let nparamsrec = mib.mind_nparams_rec in
  let (_,subst,l) =
    Context.fold_rel_context (fun (_,copt,ty) (n,substparams,l) ->
      match copt with
      | None ->
	 if n >= nparamsrec then (n,substparams,l)
	 else
	   let reif = rel_of_reifiable nparamsrec n in
	   let tyr = rel_of_param nparamsrec n in
	   let t = match oproj with
	     | Some f -> Constr.mkApp(f, [|tyr;reif|])
	     | None -> reif
	   in
	   let substparams = t :: substparams in
	   let l = (Anonymous, Constr.mkApp(Lazy.force Reifiable.t,[|Constr.mkRel 1|])) :: l in
	   let l = (Anonymous, ty) :: l in
	   (n+1,substparams,l)
      | Some _ -> assert false
    ) ctxt ~init:(0,[],[])
  in
  (Array.of_list (List.rev subst),List.rev l)

(** [export_params mib] builds a substitution for parameters of [mib] and a list
     of types of export functions. *)
let export_params mib =
  gen_params (Some (Lazy.force Reifiable.export)) mib

let import_params mib =
  gen_params (Some (Lazy.force Reifiable.import)) mib

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
  let typs = Array.init n (fun i -> type_of_export nparams (Constr.mkInd (mind,i))) in
  let substparams, lams = export_params mib in
  let bodies =
    Array.mapi (fun i -> export_inductive env ((mind,i),u) n nparams substparams) mib.mind_packets
  in
  let t = Constr.mkFix((recindexes,i),(funnames,typs,bodies)) in
  Termops.it_mkLambda t lams


(* TODO *)
let import_mind env (mind,i as ind) =
  let (mib,_) = lookup_mind_specif env ind in
  let nparams = mib.mind_nparams_rec in
  let substparams, lams = import_params mib in
  let ty = apply_params nparams (Constr.mkInd ind) in
  (* Lift corresponding to the argument (i.e. the s-expr) *)
  let ty = Vars.lift 1 ty in
  let none = Constr.mkApp(Lazy.force Init.none, [|ty|]) in
  let t = Constr.mkLambda(Anonymous, Lazy.force SExpr.t, none) in
  Termops.it_mkLambda t lams
