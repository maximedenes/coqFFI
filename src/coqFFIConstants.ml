open Constr
(** This module stores the references to Coq's namespace. *)

let message = "CoqFFI"
let lookup  = Coqlib.gen_constant_in_modules message
let lookup_ref = Coqlib.gen_reference_in_modules message

module SExpr = struct
  let constant = lookup [["CoqFFI"; "reifiable"; "SExpr"]]
  
  let t          = lazy (constant "t")
  
  let i          = lazy (constant "I")
  let b          = lazy (constant "B")
end

module Reifiable = struct
  let path = [["CoqFFI"; "reifiable"; "Reifiable"]]
  let constant = lookup path
  let reference = lookup_ref path
  
  let t          = lazy (constant "t")
  
  let import     = lazy (constant "Import")
  let export     = lazy (constant "Export")
  let export_ref = lazy (reference "Export")

  let new_reifiable = lazy (constant "New")
end

module CoqFFI = struct
  let constant = lookup [["CoqFFI"; "coqFFI"]]
end

module Init = struct
  let constant = lookup Coqlib.init_modules
  
  let bool       = lazy (constant "bool")
  let nat        = lazy (constant "nat")
  let option     = lazy (constant "option")
  
  let eq_refl    = lazy (constant "eq_refl")
  
  let _O         = lazy (constant "O")
  let _S         = lazy (constant "S")
  
  let none       = lazy (constant "None")
  let some       = lazy (constant "Some")
  
  let _nil       = lazy (constant "nil")
  let _cons      = lazy (constant "cons")
  
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

module Positive = struct
  let constant = lookup [["Coq"; "Numbers"; "BinNums"]]

  let t        = lazy (constant "positive")
  let xH       = lazy (constant "xH")
  let xI       = lazy (constant "xI")
  let xO       = lazy (constant "xO")
end

(* Interface between Coq and OCaml S-expressions *)

type sexpr =
  | I of int
  | B of sexpr * sexpr

let rec mk_positive i =
  if i > 1 then
    let digit =
      if i land 1 = 0 then Lazy.force Positive.xO
      else Lazy.force Positive.xI
    in
    Constr.mkApp(digit, [|mk_positive (i lsr 1)|])
  else Lazy.force Positive.xH

let rec mk_sexpr : sexpr -> Term.constr = function
  | I i -> Constr.mkApp(Lazy.force SExpr.i, [|mk_positive i|])
  | B (r1, r2) -> Constr.mkApp(Lazy.force SExpr.b, [|mk_sexpr r1; mk_sexpr r2|])

exception NotAnSExpr

let check_positive ind =
  if not (Constr.equal (mkInd ind) (Lazy.force Positive.t)) then
    raise NotAnSExpr

let check_sexpr_ind ind =
  if not (Constr.equal (mkInd ind) (Lazy.force SExpr.t)) then
    raise NotAnSExpr

let rec int_of_positive acc t =
  match Constr.kind t with
  | Construct ((ind,3),_) -> (* xH *)
     check_positive ind; acc
  | App(f,args) ->
     begin match Constr.kind f with
     | Construct ((ind,i),_) -> (* xI (i = 1) or xO (i = 2) *)
	check_positive ind;
	if Int.equal (Array.length args) 1 && 1 <= i && i <= 2 then
	  int_of_positive (2 * acc + (i mod 2)) args.(0)
	else raise NotAnSExpr
     | _ -> raise NotAnSExpr
     end
  | _ -> raise NotAnSExpr

let int_of_positive t = int_of_positive 1 t

let rec sexpr_of_coq_sexpr t =
  match Constr.kind t with
  | App(f,args) ->
     begin match Constr.kind f with
     | Construct ((ind,1),_) ->
	check_positive ind;
	if Int.equal (Array.length args) 1 then
          I(int_of_positive args.(0))
	else raise NotAnSExpr
     | Construct ((ind,2),_) ->
	check_sexpr_ind ind;
	if Int.equal (Array.length args) 2 then
          B(sexpr_of_coq_sexpr args.(0),sexpr_of_coq_sexpr args.(1))
	else raise NotAnSExpr
     | _ -> raise NotAnSExpr
     end
  | _ -> raise NotAnSExpr
