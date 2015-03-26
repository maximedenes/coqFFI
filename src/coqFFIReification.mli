open Environ
open Names
open Constr

val export_mind : env -> (MutInd.t * int) * Univ.universe_instance -> constr
val import_inductive : 'a -> Names.inductive -> Constr.constr
