open OcamlbindConstants

val register_fun : string -> (sexpr -> sexpr) -> unit

val get_fun : string -> (sexpr -> sexpr)

(* These are temporary and unsafe *)
val get_input : unit -> sexpr

val save_input : 'a -> unit
