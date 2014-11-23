open OcamlbindConstants

type sexpr =
  | I
  | B of sexpr * sexpr

let rec mk_sexpr : sexpr -> Term.constr = function
  | I -> Lazy.force SExpr.i
  | B (r1, r2) -> Term.mkApp (Lazy.force SExpr.b, [| mk_sexpr r1; mk_sexpr r2 |])

let registered_funs = (Hashtbl.create 17 : (string, sexpr -> sexpr) Hashtbl.t)

let register_fun id f = Hashtbl.add registered_funs id f
			
let get_fun id = Hashtbl.find registered_funs id

let output = ref I

let save_output x = output := x

let get_output () = !output
