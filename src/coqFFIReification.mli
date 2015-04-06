open Environ
open Names
open Constr

val encode_mind : env -> pinductive -> constr
val decode_mind : env -> pinductive -> constr
