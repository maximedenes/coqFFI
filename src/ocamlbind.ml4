open Tactics
open Tacticals
open Refiner
open Tacmach
open Entries
open Declarations
open Declare

open OcamlbindConstants
open OcamlbindState

(** Use site configuration to determine where OCamlBind
    is installed. *)
let coqlib =
    Filename.concat (Filename.concat (Envars.coqlib ()) "user-contrib") "OCamlBind"

(** Use site configuration to use the right ocaml native compilers. *)
let ocamlopt = Envars.ocamlopt ()

(** Use site configuration to use the right ocaml bytecode compilers. *)
let ocamlc = Envars.ocamlc ()

(** [command s] runs [s] and logs the exit status. *)
let command s =
  let ret = Sys.command s in
  Pp.msg (Pp.str (Printf.sprintf "OCamlBind [%d]: %s\n" ret s))

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

(** [define c] introduces a fresh constant name for the term [c]. *)
let define c =
  let fresh_name =
    let base = Names.id_of_string "ocamlbind_main" in

  (** [is_visible_name id] returns [true] if [id] is already
      used on the Coq side. *)
    let is_visible_name id =
      try
        ignore (Nametab.locate (Libnames.qualid_of_ident id));
        true
      with Not_found -> false
    in
    (** Safe fresh name generation. *)
    Namegen.next_ident_away_from base is_visible_name
  in
  ignore (
    declare_constant ~internal:KernelVerbose fresh_name
      (DefinitionEntry (definition_entry c),
       Decl_kinds.IsDefinition Decl_kinds.Definition)
  );
  fresh_name

(** compile [c] returns a compiled version of the monadic computation [c]
    in the form of an Ocaml module. *)
let compile c =
  print_endline message;
  let rec compile () =
    (** The compilation is the composition of the Coq extraction
        with the compilation from ocaml to the right low-level
        plateform (native or bytecode).

        The extraction uses a temporary definition that is automatically
        cleaned up using the Coq's rollback mechanism.
    *)
    ocaml_compiler (States.with_state_protection ocaml_via_extraction ())

  and ocaml_via_extraction () =
    (** Name [c]. *)
    let constant = define c in
    (** Extract [c] in a file and all its dependencies. *)
    let tmp      = Filename.temp_file "ocamlbind" ".ml" in
    let tmp_intf = Filename.chop_extension tmp ^ ".mli" in
    Extract_env.full_extraction (Some tmp) [
      Libnames.Ident (Loc.ghost, constant)
    ];
    (** We are not interested in the interface file. *)
    cleanup tmp_intf;
    tmp

  and ocaml_compiler fname =
    (** Use a temporary file for the compiled module. *)
    let compiled_module =
      let basename = Filename.temp_file "ocamlbind_dyn" "" in
      fun ext -> basename ^ "." ^ ext 
    in
    (** Compile using the right compiler. *)
    if Dynlink.is_native then (
        let target  = compiled_module "cmx" in
        let target' = compiled_module "cmxs" in
        command (Printf.sprintf
                   "%s -rectypes -c -I %s -o %s %s"
                   ocamlopt coqlib target fname);
        command (Printf.sprintf
                   "%s -shared -o %s %s"
                   ocamlopt target' target);
        (target', [target; target'])
    ) else (
      let target = compiled_module "cmo" in
        command (Printf.sprintf 
                   "%s -rectypes -c -linkall -I %s -o %s %s/ocamlbindPlugin.cma %s"
                   ocamlc coqlib target coqlib fname);
        (target, [target])
    )
  in
  compile ()

let dynload f =
  try
    Dynlink.loadfile f
  with Dynlink.Error e ->
    Errors.error ("OCamlBind (during compiled code loading):"
                   ^ (Dynlink.error_message e))

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

let ocamlbind f a =
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    (*
    let c = Term.mkApp (Lazy.force OCamlbind.save_input,  [|a|]) in
    let dyncode, files = compile c in
    dynload dyncode;
    let a = get_input () in
    *)
    let t1 = time "apply import" (fun () -> apply (Lazy.force Reifiable.import)) in
    let f = get_fun f in
    let a = time "normalize" (fun () -> Redexpr.cbv_vm env sigma a) in
    let a = time "convert sexpr" (fun () -> sexpr_of_coq_sexpr a) in
    let r = time "apply function" (fun () -> f a) in
    let r = time "mk_sexpr" (fun () -> mk_sexpr r) in
    let t2 = time "apply term" (fun () -> apply r) in
    Tacticals.New.tclTHENLIST [ t1; solve_remaining_apply_goals; t2 ]
  end

let ocamlrun f a =
  (* Code taken from vernac_global_check in toplevel/vernacexpr.ml *)
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (c,ctx) = Constrintern.interp_constr env sigma a in
  let senv = Global.safe_env() in
  let cstrs = snd (Evd.evar_universe_context_set ctx) in
  let senv = Safe_typing.add_constraints cstrs senv in
  (* TODO
  let ty = Safe_typing.j_type (Safe_typing.typing senv c) in
  let c = Term.mkApp (Lazy.force OCamlbind.save_input_unsafe,  [|ty;c|]) in
  *)
  let dyncode, files = compile c in
  dynload dyncode;
  let a = get_input () in
  (* let a = sexpr_of_coq_sexpr c in *)
  let f = get_fun f in
  let _ = f a in ()

let _ = register_fun "id" (fun x -> x)

DECLARE PLUGIN "ocamlbindPlugin"

TACTIC EXTEND ocamlbind
  [ "ocamlbind" string(f) constr(a) ] -> [ ocamlbind f a ]
END

VERNAC COMMAND EXTEND OCamlrun CLASSIFIED AS QUERY
  [ "OCamlrun" string(f) constr(a) ] -> [ ocamlrun f a ]
END
