(*

(* 1 Type inference for a simply typed calculus *)

let () = Printexc.record_backtrace true

type tvar = string

type var = string

(* 1.1 Simple types *)

type ty =
  | TyVar of tvar
  | TyArrow of ty * ty

(* 1.2 λ-terms *)

type tm =
  | TmVar of var * ty
  | TmAbs of var * ty * tm
  | TmApp of tm * tm

(* 1.3 String representation *)

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

(* 1.4 Type inference *)

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

(* WORKING
(* λf : A. x *)
let invalid_term_1 = TmAbs ("f", TyVar "A", TmVar ("x", TyVar "A"))
let error1 = infer_type ctx invalid_term_1


(* λf : A. λx : B. f x *)
let invalid_term_2 = TmAbs ("f", TyVar "A", TmAbs ("x", TyVar "B", TmApp (TmVar ("f", TyVar "A"), TmVar ("x", TyVar "B"))))
let error2 = infer_type ctx invalid_term_2


(* λf : A -> B. λx : B. f x *)
let invalid_term_3 = TmAbs ("f", TyArrow (TyVar "A", TyVar "B"), TmAbs ("x", TyVar "B", TmApp (TmVar ("f", TyArrow (TyVar "A", TyVar "B")), TmVar ("x", TyVar "B"))))
let error3 = infer_type ctx invalid_term_3
*)

(* 1.5 Type checking *)

let check_type (ctx : context) (term : tm) (expected_ty : ty) : unit =
  match infer_type ctx term with
  | inferred_ty when inferred_ty = expected_ty -> ()
  | _ -> raise Type_error

  let test_check_type () =

    let term1 = TmAbs ("x", TyVar "A", TmVar ("x", TyVar "A")) in
    let expected_ty1 = TyArrow (TyVar "A", TyVar "A") in
    match check_type [] term1 expected_ty1 with
    | () -> print_endline "Test 1 passed: λ(x : A). x has type A → A"
    | exception Type_error -> print_endline "Test 1 failed: λ(x : A). x has type A → A"

    let expected_ty2 = TyArrow (TyVar "B", TyVar "B") in
    match check_type [] term1 expected_ty2 with
    | () -> print_endline "Test 2 failed: λ(x : A). x does not have type B → B"
    | exception Type_error -> print_endline "Test 2 passed: λ(x : A). x does not have type B → B";
  
    let term3 = TmVar ("x", TyVar "A") in
    let expected_ty3 = TyVar "A" in
    match check_type [] term3 expected_ty3 with
    | () -> print_endline "Test 3 failed: x does not have type A"
    | exception Type_error -> print_endline "Test 3 passed: x does not have type A"
  
(* 1.6 Type inference and checking together *)

(* A FAIRE *)

*)

(* 1.7 Other connectives *)

(* Types étendus *)
type ty =
  | TyVar of tvar
  | TyArrow of ty * ty
  | TyProd of ty * ty    (* Produit A × B *)
  | TySum of ty * ty     (* Somme A + B *)
  | TyUnit              (* Unité 1 *)
  | TyZero              (* Zéro 0 *)

(* Termes étendus *)
type tm =
  | TmVar of var * ty
  | TmAbs of var * ty * tm
  | TmApp of tm * tm
  | TmPair of tm * tm         (* (t1, t2) : A × B *)
  | TmProj1 of tm             (* π1 t *)
  | TmProj2 of tm             (* π2 t *)
  | TmInl of tm * ty          (* inl t : A + B *)
  | TmInr of tm * ty          (* inr t : A + B *)
  | TmCase of tm * (var * tm) * (var * tm)  (* case t of inl x -> u | inr y -> v *)
  | TmUnit                   (* unité : 1 *)
  | TmZeroCase of tm          (* case t : 0 -> A *)

(* Inférence de type étendue *)
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
      (match ty1 with
       | TyArrow (arg_ty, res_ty) when arg_ty = ty2 -> res_ty
       | _ -> raise Type_error)
  | TmPair (t1, t2) ->
      let ty1 = infer_type ctx t1 in
      let ty2 = infer_type ctx t2 in
      TyProd (ty1, ty2)
  | TmProj1 t ->
      (match infer_type ctx t with
       | TyProd (ty1, _) -> ty1
       | _ -> raise Type_error)
  | TmProj2 t ->
      (match infer_type ctx t with
       | TyProd (_, ty2) -> ty2
       | _ -> raise Type_error)
  | TmInl (t, TySum (ty1, _)) ->
      let t_ty = infer_type ctx t in
      if t_ty = ty1 then TySum (ty1, t_ty)
      else raise Type_error
  | TmInr (t, TySum (_, ty2)) ->
      let t_ty = infer_type ctx t in
      if t_ty = ty2 then TySum (t_ty, ty2)
      else raise Type_error
  | TmCase (t, (x, u), (y, v)) ->
      (match infer_type ctx t with
       | TySum (ty1, ty2) ->
           let ty_u = infer_type ((x, ty1) :: ctx) u in
           let ty_v = infer_type ((y, ty2) :: ctx) v in
           if ty_u = ty_v then ty_u
           else raise Type_error
       | _ -> raise Type_error)
  | TmUnit -> TyUnit
  | TmZeroCase t ->
      (match infer_type ctx t with
       | TyZero -> TyZero
       | _ -> raise Type_error)

(* Ajout des tests *)
let test () =
  (* Test produit *)
  let term_prod = TmPair (TmVar ("x", TyVar "A"), TmVar ("y", TyVar "B")) in
  let ctx = [("x", TyVar "A"); ("y", TyVar "B")] in
  let inferred_prod_ty = infer_type ctx term_prod in
  assert (inferred_prod_ty = TyProd (TyVar "A", TyVar "B"));

  (* Test somme *)
  let term_sum = TmInl (TmVar ("x", TyVar "A"), TySum (TyVar "A", TyVar "B")) in
  let inferred_sum_ty = infer_type ctx term_sum in
  assert (inferred_sum_ty = TySum (TyVar "A", TyVar "B"));

  (* Test unité *)
  let term_unit = TmUnit in
  let inferred_unit_ty = infer_type [] term_unit in
  assert (inferred_unit_ty = TyUnit);

  (* Test zéro *)
  let term_zero_case = TmZeroCase (TmVar ("z", TyZero)) in
  let inferred_zero_ty = infer_type [("z", TyZero)] term_zero_case in
  assert (inferred_zero_ty = TyZero);

  print_endline "All tests passed!"
