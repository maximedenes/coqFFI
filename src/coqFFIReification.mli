open Environ
open Names
open Constr

val export_mind : env -> (MutInd.t * int) * Univ.universe_instance -> constr
val import_mind : env -> Names.inductive -> Constr.constr

val gen_params : constr option -> Declarations.mutual_inductive_body ->
		 constr array * (name * constr) list
val apply_params : int -> constr -> constr
val apply_reifiables : int -> constr -> constr
