open Environ
open Names
open Constr

val export_mind : env -> (MutInd.t * int) * Univ.universe_instance -> constr
val import_mind : env -> Names.inductive -> Constr.constr

val apply_params : constr list -> constr -> constr
