open Names
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
open Globnames

open CoqFFIConstants
open CoqFFIState
open CoqFFIReification

(** Use site configuration to determine where CoqFFI
    is installed. *)
let coqlib =
    Filename.concat (Filename.concat (Envars.coqlib ()) "user-contrib") "CoqFFI"

(** Use site configuration to use the right ocaml native compilers. *)
let ocamlopt = Envars.ocamlopt ()

(** Use site configuration to use the right ocaml bytecode compilers. *)
let ocamlc = Envars.ocamlc ()

(** [command s] runs [s] and logs the exit status. *)
let command s =
  let ret = Sys.command s in
  Pp.msg (Pp.str (Printf.sprintf "CoqFFI [%d]: %s\n" ret s))

let cleanup fname =
  command (Printf.sprintf "rm %s" fname)

(** [time l f] runs [f ()] displaying its running time. *)
let time l f =
  let start = System.get_time () in
  let y = f () in
  let stop = System.get_time () in
  Pp.msg_info (Pp.str
                 (Printf.sprintf "Running time of the %s: %f secs\n"
                    l
                    (System.time_difference start stop)));
  y

let solve_remaining_apply_goals =
  Proofview.Goal.nf_enter begin fun gl ->
    try 
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      if Typeclasses.is_class_type sigma concl then
        let evd', c' = Typeclasses.resolve_one_typeclass env sigma concl in
    Tacticals.New.tclTHEN
          (Proofview.Unsafe.tclEVARS evd')
          (Proofview.V82.tactic (refine_no_check c'))
    else Proofview.tclUNIT ()
    with Not_found -> Proofview.tclUNIT ()
  end

let define name c =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (evd,_) = Typing.type_of env evd c in
  let uctxt = Evd.evar_context_universe_context (Evd.evar_universe_context evd) in
  (* We use [UserIndividualRequest] to show errors at declaration time. for
  debugging purposes. The final value of this flag should probably be
  [InternalTacticRequest] *)
  declare_constant ~internal:UserIndividualRequest name
      (DefinitionEntry (definition_entry ~univs:uctxt c),
       Decl_kinds.IsDefinition Decl_kinds.Definition)

(* Convert the constr [a] to an S-expression, apply [f] to it and converts the
   resulting S-expression back to a constr. *)
(* TODO: register the type of the function represented by [f] and check *)
(* that the one of [a] and of the goal are compatible. *)
let bindForeign f a =
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let t1 = time "apply import" (fun () -> apply (Lazy.force Decodable.decode)) in
    let f = get_fun f in
    let a = time "normalize" (fun () -> Redexpr.cbv_vm env sigma a) in
    let a = time "convert sexpr" (fun () -> sexpr_of_coq_sexpr a) in
    let r = time "apply function" (fun () -> f a) in
    let r = time "mk_sexpr" (fun () -> mk_sexpr r) in
    let t2 = time "apply term" (fun () -> apply r) in
    Tacticals.New.tclTHENLIST [ t1; solve_remaining_apply_goals; t2 ]
  end

(* Convert the constr_expr [c] to an S-expression and apply [f] to it. *)
(* The result is ignored. *)
(* TODO: register the type of the function represented by [f] and check *)
(* that the one of [c] is compatible. *)
let runForeign f c =
  let encode = Lazy.force Encodable.encode_ref in
  let encode = CRef(global_ref_of_ref encode, None) in
  let c = CApp(Loc.ghost, (None,encode), [(c,None)]) in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (c,ctx) = interp_constr env evd c in
  let c = Redexpr.cbv_vm env evd c in
  (* Pp.ppnl (Termops.print_constr c); *)
  let c = sexpr_of_coq_sexpr c in
  let f = get_fun f in
  let _ = f c in ()

let encodable_class =
  lazy (let Some (_, ((encodable,_), _)) = Typeclasses.class_of_constr (Lazy.force Encodable.t) in
  encodable)

let decodable_class =
  lazy (let Some (_, ((decodable,_), _)) = Typeclasses.class_of_constr (Lazy.force Decodable.t) in
  decodable)

let reification_gen r =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let ind = global_inductive r in
  let (mib,_) = lookup_mind_specif env ind in
  let nparams = mib.mind_nparams_rec in
  let pind, ctxt = Universes.fresh_inductive_instance env ind in
  Global.push_context_set false ctxt;
  let env = Global.env () in
  let evd = Evd.from_env env in
  let base = basename_of_global (IndRef ind) in
  let name_export = add_suffix base "_export" in
  let name_import = add_suffix base "_import" in
  let name_reify = add_suffix base "_reify" in
  let export_term = encode_mind env pind in
  (* Pp.ppnl (Termops.print_constr export_term); *)
  let export = define name_export export_term in
  let export = global_ref_of_ref (ConstRef export) in
  Classes.existing_instance true export None;
  Pp.msg_info (Pp.str (Printf.sprintf "Defined export function for %s\n"
                         (MutInd.to_string (fst ind))));
  let import_term = decode_mind env pind in
  (* Pp.ppnl (Termops.print_constr import_term); *)
  let import = define name_import import_term in
  let import = global_ref_of_ref (ConstRef import) in
  Classes.existing_instance true import None;
  Pp.msg_info (Pp.str (Printf.sprintf "Defined import function for %s\n"
                         (MutInd.to_string (fst ind))))

(* For debug printers *)
let _ = Detyping.set_detype_anonymous (fun _ _ -> raise Not_found)

let _ = register_fun "id" (fun x -> x)

DECLARE PLUGIN "coqFFIPlugin"

TACTIC EXTEND coqFFI
  [ "bindForeign" string(f) constr(a) ] -> [ bindForeign f a ]
END

VERNAC COMMAND EXTEND RunForeign CLASSIFIED AS QUERY
  [ "RunForeign" string(f) constr(a) ] -> [ runForeign f a ]
END

VERNAC COMMAND EXTEND Reification CLASSIFIED AS QUERY
  [ "Reification" "for" global(r) ] -> [ reification_gen r ]
END
