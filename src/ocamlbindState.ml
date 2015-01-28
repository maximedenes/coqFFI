open Errors
open Names
open Constr
open OcamlbindConstants

let registered_funs = (Hashtbl.create 17 : (string, sexpr -> sexpr) Hashtbl.t)

let register_fun id f = Hashtbl.add registered_funs id f

let get_fun id =
  try Hashtbl.find registered_funs id
  with Not_found ->
    (Errors.error ("Function \"" ^ id ^ "\" was not registered."); fun x -> x)

let get_fun_unsafe id =
  try Obj.magic (Hashtbl.find registered_funs id)
  with Not_found ->
    (Errors.error ("Function \"" ^ id ^ "\" was not registered."); fun x -> x)

let input = ref I

let save_input x = input := (Obj.magic x)

let get_input () = !input
