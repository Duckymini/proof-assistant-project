let () = Printexc.record_backtrace true

(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Simple types. *)
type ty =
  | TyVar of tvar
  | TyArrow of ty * ty

type tm =
  | TmVar of var * ty
  | TmAbs of var * ty * tm
  | TmApp of tm * tm

let rec string_of_ty ty =
  match ty with
  | TyVar t -> t
  | TyArrow (ty1, ty2) -> 
    "(" ^ string_of_ty ty1 ^ " → " ^ string_of_ty ty2 ^ ")"


let rec string_of_tm tm =
  match tm with
  | TmVar (v, ty) -> v ^ " : " ^ string_of_ty ty
  | TmAbs (v, ty, tm) -> 
    "(λ (" ^ v ^ " : " ^ string_of_ty ty ^ ") -> " ^ string_of_tm tm ^ ")"
  |TmApp (tm1, tm2) ->
    "(" ^ string_of_tm tm1 ^ " " ^ string_of_tm tm2 ^ ")"

(* Let's test our two function *)
let example_type = TyArrow (TyArrow (TyVar "A", TyVar "B"), TyArrow (TyVar "A", TyVar "C"))
let type_str = string_of_ty example_type

let example_term =
  TmAbs ("f", TyArrow (TyVar "A", TyVar "B"),         (* fun (f : (A => B)) *)
    TmAbs ("x", TyVar "A",                            (* fun (x : A) *)
      TmApp (TmVar ("f", TyArrow (TyVar "A", TyVar "B")), TmVar ("x", TyVar "A"))  (* f x *)
    )
  )
let term_str = string_of_tm example_term


type context = (var * ty) list

exception Type_error

let rec infer_type (ctx : context) (t : tm) : ty =
  match t with
  | TmVar (v, _) -> (
    try List.assoc v ctx
    with Not_found -> raise Type_error
  )
  | TmAbs (v, ty, body) ->
    let extended_ctx = (v, ty) :: ctx in
    let body_ty = infer_type extended_ctx body in
    TyArrow (ty, body_ty)
  | TmApp (t1, t2) ->
    let ty1 = infer_type ctx t1 in
    let ty2 = infer_type ctx t2 in
    match ty1 with
      | TyArrow (arg_ty, res_ty) when arg_ty = ty2 -> res_ty
      | _ -> raise Type_error

let example_term =
  TmAbs ("f", TyArrow (TyVar "A", TyVar "B"),
    TmAbs ("g", TyArrow (TyVar "B", TyVar "C"),
      TmAbs ("x", TyVar "A",
        TmApp (
          TmVar ("g", TyArrow (TyVar "B", TyVar "C")),
          TmApp (TmVar ("f", TyArrow (TyVar "A", TyVar "B")), TmVar ("x", TyVar "A"))
        )
      )
    )
  )
      
let ctx = []
let inferred_type = infer_type ctx example_term
let term_str = string_of_ty inferred_type


(* (* λf : A. x *)
let invalid_term_1 = TmAbs ("f", TyVar "A", TmVar ("x", TyVar "A"))

try
  let ty = infer_type ctx invalid_term_1 in
  print_endline "No error raised (unexpected)"
with 
  | Type_error -> print_endline "Type_error raised (expected)"


λf : A. λx : B. f x
let invalid_term_2 =
  TmAbs ("f", TyVar "A", TmAbs ("x", TyVar "B", TmApp (TmVar ("f", TyVar "A"), TmVar ("x", TyVar "B"))))

try
  let _ = infer_type [] invalid_term_2 in
  print_endline "No error raised (unexpected)"
with Type_error -> print_endline "Type_error raised (expected)"


(* λf : A -> B. λx : B. f x *)
let invalid_term_3 =
  TmAbs ("f", TyArrow (TyVar "A", TyVar "B"), TmAbs ("x", TyVar "B", TmApp (TmVar ("f", TyArrow (TyVar "A", TyVar "B")), TmVar ("x", TyVar "B"))))

try
  let _ = infer_type [] invalid_term_3 in
  print_endline "No error raised (unexpected)"
with Type_error -> print_endline "Type_error raised (expected)" *)


let check_type (ctx : context) (term : tm) (expected_ty : ty) : unit =
  let inferred_ty = infer_type ctx term in
  if inferred_ty = expected_ty then
    ()
  else
    raise Type_error
