open Constr
(** This module stores the references to Coq's namespace. *)

let message = "OCamlBind"
let lookup  = Coqlib.gen_constant_in_modules message

module SExpr = struct
  let constant = lookup [["OCamlBind"; "reifiable"; "SExpr"]]
  
  let t          = lazy (constant "t")
  
  let i          = lazy (constant "I")
  let b          = lazy (constant "B")
end

module Reifiable = struct
  let constant = lookup [["OCamlBind"; "reifiable"; "Reifiable"]]
  
  let t          = lazy (constant "t")
  
  let import     = lazy (constant "Import")
end

module OCamlbind = struct
  let constant = lookup [["OCamlBind"; "ocamlbind"]]

  let save_input = lazy (constant "save_input")

  let save_input_unsafe = lazy (constant "save_input_unsafe")
end

module Init = struct
  let init_constant = lookup Coqlib.init_modules
  
  let bool       = lazy (init_constant "bool")
  let nat        = lazy (init_constant "nat")
  let option     = lazy (init_constant "option")
  
  let eq_refl    = lazy (init_constant "eq_refl")
  
  let _O         = lazy (init_constant "O")
  let _S         = lazy (init_constant "S")
  
  let none       = lazy (init_constant "None")
  let some       = lazy (init_constant "Some")
  
  let _nil       = lazy (init_constant "nil")
  let _cons      = lazy (init_constant "cons")
  
  let rec mk_nat = function
    | 0 -> Lazy.force _O
    | n -> Term.mkApp (Lazy.force _S, [| mk_nat (pred n) |])
  
  let mk_option typ (mk : 'a -> Term.constr) : 'a option -> Term.constr = function
    | None -> Term.mkApp (Lazy.force none, [| typ |])
    | Some x -> Term.mkApp (Lazy.force some, [| typ; mk x |])
  
  let rec mk_list typ (mk : 'a -> Term.constr) : 'a list -> Term.constr = function
    | [] -> Term.mkApp (Lazy.force _nil, [| typ |])
    | x :: xs -> Term.mkApp (Lazy.force _cons, [| typ; mk x; mk_list typ mk xs |])

end

(* Interface between Coq and OCaml S-expressions *)

type sexpr =
  | I
  | B of sexpr * sexpr

let rec mk_sexpr : sexpr -> Term.constr = function
  | I -> Lazy.force SExpr.i
  | B (r1, r2) -> Term.mkApp (Lazy.force SExpr.b, [| mk_sexpr r1; mk_sexpr r2 |])

exception NotAnSExpr

let check_sexpr_ind ind =
  if not (Constr.equal (mkInd ind) (Lazy.force SExpr.t)) then
    raise NotAnSExpr

let rec sexpr_of_coq_sexpr t =
  match Constr.kind t with
  | Construct ((ind,1),_) ->
     check_sexpr_ind ind; I
  | App(f,args) ->
     begin match Constr.kind f with
     | Construct ((ind,2),_) ->
	check_sexpr_ind ind;
	if Int.equal (Array.length args) 2 then
          B(sexpr_of_coq_sexpr args.(0),sexpr_of_coq_sexpr args.(1))
	else raise NotAnSExpr
     | _ -> raise NotAnSExpr
     end
  | _ -> raise NotAnSExpr
