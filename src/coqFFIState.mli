open CoqFFIConstants

val register_fun : string -> (sexpr -> sexpr) -> unit

val get_fun : string -> (sexpr -> sexpr)
