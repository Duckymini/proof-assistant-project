(* 1 Type inference for a simply typed calculus *)

let () = Printexc.record_backtrace true

type tvar = string

type var = string

(* 1.1 Simple types *)

type ty =
  | TyVar of tvar
  | TyArrow of ty * ty
  | TyProd of ty * ty    (* Produit A × B *)
  | TySum of ty * ty     (* Somme A + B *)
  | TyUnit              (* Unité 1 *)
  | TyZero              (* Zéro 0 *)
  | TyAnd of ty * ty
  | TyTrue
  | TyFalse
  | TyOr of ty * ty

(* 1.2 λ-terms *)

type tm =
  | TmVar of var * ty
  | TmAbs of var * ty * tm
  | TmApp of tm * tm
  | TmPair of tm * tm         (* (t1, t2) : A × B *)
  | TmProj1 of tm             (* π1 t *)
  | TmProj2 of tm             (* π2 t *)
  (*| TmInl of tm * ty          (* inl t : A + B *)
  | TmInr of tm * ty          (* inr t : A + B *) *)
  | TmCase of tm * (var * tm) * (var * tm)  (* case t of inl x -> u | inr y -> v *)
  | TmUnit                   (* unité : 1 *)
  | TmZeroCase of tm          (* case t : 0 -> A *)
  | TmAndIntro of tm * tm    (* Introduction of A /\ B *)
  | TmAndElimL of tm         (* Elimination of A /\ B to A *)
  | TmAndElimR of tm         (* Elimination of A /\ B to B *)
  | TmTrue
  | TmFalse
  | TmExFalso of tm * ty
  | TmLeft of tm * ty           (* Left term in A \/ B *)
  | TmRight of tm * ty          (* Right term in A \/ B *)
  | TmOrCase of tm * (var * tm) * (var * tm)
  | TmAbsurd of tm * ty (* Represents abusrd *)
  

(* 1.3 String representation *)

let rec string_of_ty ty =
  match ty with
  | TyVar t -> t
  | TyArrow (ty1, ty2) -> "(" ^ string_of_ty ty1 ^ " → " ^ string_of_ty ty2 ^ ")"
  | TyProd (ty1, ty2) -> "(" ^ string_of_ty ty1 ^ " × " ^ string_of_ty ty2 ^ ")"
  | TySum (ty1, ty2) -> "(" ^ string_of_ty ty1 ^ " + " ^ string_of_ty ty2 ^ ")"
  | TyUnit -> "1"
  | TyZero -> "0"
  | TyAnd (ty1, ty2) -> "(" ^ string_of_ty ty1 ^ " ∧ " ^ string_of_ty ty2 ^ ")"
  | TyTrue -> "⊤"
  | TyFalse -> "⊥"
  | TyOr (ty1, ty2) -> "(" ^ string_of_ty ty1 ^ " ∨ " ^ string_of_ty ty2 ^ ")"
  
let rec string_of_tm tm =
  match tm with
  | TmVar (v, ty) -> v ^ " : " ^ string_of_ty ty
  | TmAbs (v, ty, tm) -> "(λ (" ^ v ^ " : " ^ string_of_ty ty ^ ") -> " ^ string_of_tm tm ^ ")"
  | TmApp (tm1, tm2) -> "(" ^ string_of_tm tm1 ^ " " ^ string_of_tm tm2 ^ ")"
  | TmPair (tm1, tm2) -> "(" ^ string_of_tm tm1 ^ ", " ^ string_of_tm tm2 ^ ")"
  | TmProj1 tm -> "π1(" ^ string_of_tm tm ^ ")"
  | TmProj2 tm -> "π2(" ^ string_of_tm tm ^ ")"
  (*
  | TmInl (tm, ty) -> "inl " ^ string_of_tm tm ^ " : " ^ string_of_ty ty
  | TmInr (tm, ty) -> "inr " ^ string_of_tm tm ^ " : " ^ string_of_ty ty *)
  | TmCase (tm, (x, u), (y, v)) ->
      "case " ^ string_of_tm tm ^ " of inl " ^ x ^ " -> " ^ string_of_tm u ^
      " | inr " ^ y ^ " -> " ^ string_of_tm v
  | TmUnit -> "()"
  | TmZeroCase tm -> "case_zero(" ^ string_of_tm tm ^ ")"
  | TmAndIntro (tm1, tm2) -> "(∧_intro " ^ string_of_tm tm1 ^ ", " ^ string_of_tm tm2 ^ ")"
  | TmAndElimL tm -> "(∧_elim_L " ^ string_of_tm tm ^ ")"
  | TmAndElimR tm -> "(∧_elim_R " ^ string_of_tm tm ^ ")"
  | TmTrue -> "true"
  | TmFalse -> "false"
  | TmExFalso (tm, ty) -> "ex falso(" ^ string_of_tm tm ^ " : " ^ string_of_ty ty ^ ")"
  | TmOrCase (tm, (x, u), (y, v)) ->
    "case " ^ string_of_tm tm ^ " of inl " ^ x ^ " -> " ^ string_of_tm u ^ " | inr " ^ y ^ " -> " ^ string_of_tm v
  | TmLeft (tm, ty) -> "inl " ^ string_of_tm tm ^ " : " ^ string_of_ty ty
  | TmRight (tm, ty) -> "inr " ^ string_of_tm tm ^ " : " ^ string_of_ty ty
  | TmAbsurd (tm, ty) -> "absurd(" ^ string_of_tm tm ^ " : " ^ string_of_ty ty ^ ")"


