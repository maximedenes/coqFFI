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

open CoqFFIConstants
open CoqFFIState

let one = lazy (Constr.mkApp(Lazy.force SExpr.i,[|Lazy.force Positive.xH|]))

let find_reifiable_instance env ty =
  let evd = Evd.from_env env in
  (* let ctxt = Environ.empty_named_context_val in
  let (evd,ev) = Evarutil.new_pure_evar ctxt evd ty in *)
  let tc = Constr.mkApp(Lazy.force Reifiable.t, [|ty|]) in
  let (evd,constr) = Typeclasses.resolve_one_typeclass env evd tc in
  constr
(* Errors.error "Could not find an instance of reifiable" *)

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

let export_arg env nargs mind ninds ty i =
  match kind_of_term ty with
  | Constr.Ind ((mind',k),u) ->
     let arg = Constr.mkRel (nargs+1-i) in
    if MutInd.equal mind mind' then
      Constr.mkApp(Constr.mkRel (nargs+1+ninds-k), [|arg|])
    else
     (Printf.printf "mind=%s mind'=%s\n" (MutInd.to_string mind) (MutInd.to_string mind');
      let inst = find_reifiable_instance env ty in
      Constr.mkApp(Lazy.force Reifiable.export, [|ty;inst;arg|]))
  | _ -> Errors.error "applied inductive"
(*
  match kind_of_term ty with
  | Rel k -> if k > 
 *)

(** Return B tag [export_arg arg1] ... [export_arg arg2] *)
let export_constructor env mind ninds i ty =
  let ctxt,t = decompose_prod_assum ty in
  let nargs = Context.rel_context_nhyps ctxt in
  let (_,args,_) = Context.fold_rel_context (fun (_,odecl,ty) (subs,args,i) ->
    match odecl with
    | None -> (Constr.mkRel i :: subs, export_arg env nargs mind ninds ty i :: args, i+1)
    | Some b -> (Vars.substl subs b :: subs, args, i))
    ctxt ~init:([],[],1)
  in
  let tag = Constr.mkApp(Lazy.force SExpr.i, [|export_tag (i+1)|]) in
  let br = Constr.mkApp(Lazy.force SExpr.b, [|tag; export_list (List.rev args)|]) in
  (*  Pp.ppnl (Termops.print_constr br); *)
  let t = Termops.it_mkLambda_or_LetIn br ctxt in
  (*  Pp.ppnl (Termops.print_constr t); *)
  t


(** Generate the export function for the given inductive *)
(*
    fun x : ind =>
      match x return SExpr.t with
      | C0 => B [export 0] I
      | ...
      | Cn => B [export n] I
      end.
 *)
let export_inductive env ((mind,i as ind),u as pind) ninds oib =
  let ci = make_case_info env ind RegularStyle in
  let typs = arities_of_constructors env pind in
  let ty = Constr.mkInd ind in
  let p = Constr.mkLambda(Anonymous, ty, Lazy.force SExpr.t) in
  let c = Constr.mkRel 1 in
  let ac = Array.mapi (export_constructor env mind ninds) typs in
  let case = Constr.mkCase(ci,p,c,ac) in
  Constr.mkLambda(Anonymous, ty, case)

let type_of_export ty =
  Constr.mkProd(Anonymous,ty,Lazy.force SExpr.t)

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
  let typs = Array.init n (fun i -> type_of_export (Constr.mkInd (mind,i))) in
  let bodies =
    Array.mapi (fun i -> export_inductive env ((mind,i),u) n) mib.mind_packets
  in
  Constr.mkFix((recindexes,i),(funnames,typs,bodies))


(* TODO *)
let import_inductive env ind =
  let ty = Constr.mkInd ind in
  let none = Constr.mkApp(Lazy.force Init.none, [|ty|]) in
  Constr.mkLambda(Anonymous, Lazy.force SExpr.t, none)
