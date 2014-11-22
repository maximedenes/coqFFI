type sexpr

let registered_funs = (Hashtbl.create 17 : (string, sexpr -> sexpr) Hashtbl.t)

let register_fun id f = Hashtbl.add registered_funs id f
			
let get_fun id = Hashtbl.find registered_funs id
