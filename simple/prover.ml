open Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)
let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

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

(*
WORKS, but now implemented with check_type mutually recursive 

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
*)



(* 1.5 Type cheking *)

(*
WORKS, but now implemeted mutually recursive with infer_type

let check_type (ctx : context) (term : tm) (expected_ty : ty) : unit =
  match infer_type ctx term with
  | inferred_ty when inferred_ty = expected_ty -> ()
  | _ -> raise Type_error
*)

(* 1.6 Type inference and checking together *)

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
      (match ty1 with
       | TyArrow (arg_ty, res_ty) ->
           check_type ctx t2 arg_ty; (* Use check_type to validate t2 (same for the others) *)
           res_ty
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
  (* | TmInl (t, ty) ->
    (match ty with
    | TySum (ty1, ty2) -> 
      check_type ctx t ty1;
      TySum (ty1, ty2)
    | _ -> raise Type_error) *)
  (*| TmInr (t, ty) ->
    (match ty with 
    | TySum (ty1, ty2) ->
      check_type ctx t ty2;
      TySum (ty1, ty2)
    | _ -> raise Type_error)*)
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
  | TmAndIntro (t1, t2) ->
    let ty1 = infer_type ctx t1 in
    let ty2 = infer_type ctx t2 in
    TyAnd (ty1, ty2)
  | TmAndElimL t -> (
        match infer_type ctx t with
        | TyAnd (ty1, _) -> ty1
        | _ -> raise Type_error
      )
  | TmAndElimR t -> (
      match infer_type ctx t with
      | TyAnd (_, ty2) -> ty2
      | _ -> raise Type_error
      )
  | TmTrue -> TyTrue
  | TmFalse -> TyFalse
  | TmExFalso (t, ty) ->
        (match infer_type ctx t with
         | TyFalse -> ty
         | _ -> raise Type_error)
  | TmLeft (t, ty) ->
    (match ty with
    | TyOr (ty1, _) ->
      check_type ctx t ty1;
      TyOr (ty1, TyVar "_")
    | _ -> raise Type_error)
  | TmRight (t, ty) ->
    (match ty with
    | TyOr (_ , ty2) ->
      check_type ctx t ty2;
      TyOr (TyVar "_", ty2)
    | _ -> raise Type_error)
  | TmOrCase (t, (x, u), (y, v)) ->
    (match infer_type ctx t with
    | TyOr (ty1, ty2) ->
      let ty_u = infer_type ((x, ty1) :: ctx) u in
      let ty_v = infer_type ((y, ty2) :: ctx) v in
      if ty_u = ty_v then ty_u
      else raise Type_error
    | _ -> raise Type_error) 
  | TmAbsurd (t , ty) -> 
    match infer_type ctx t with 
      | TyFalse -> ty
      | _ -> raise Type_error
      

and check_type (ctx : context) (term : tm) (expected_ty : ty) : unit =
  match infer_type ctx term with
  | inferred_ty when inferred_ty = expected_ty -> ()
  | _ -> raise Type_error


(* 1.7 Other connectives 

I've added some new ty and tm types : TyProd, TySum, TyUnit and TyZero 
and a lot of tm that will be useful for the next functions. Not sure if 
everything is correct but it runs.

*)

(* 1.8 Conjunction *)

(* I've added TyAdd and TmAndIntro, TmAndElimL and TmAndIntroR.
   I also modified infer_type (reccursive with check_type).
   Finally, let's code and_comm *)

let and_comm =
  TmAbs ("p", TyAnd (TyVar "A", TyVar "B"),
    TmAndIntro (
      TmAndElimR (TmVar ("p", TyAnd (TyVar "A", TyVar "B"))),
      TmAndElimL (TmVar ("p", TyAnd (TyVar "A", TyVar "B")))
    )
  )

let () =
  let ty = infer_type [] and_comm in
  print_endline (string_of_ty ty)

(* We have the expected print *)

(* 1.9 Truth, 1.10 Disjunction and 1.11 Falsity *)

(* We added TyTrue, TyFalse and TyOr, TmTrue, TmFalse, TmExFalso, TmLeft, TmRight and TmOrCase,
   modified the strings representations and the infer_type function *)

let tru_comm =
  TmAbs ("x", TyArrow (TyTrue, TyVar "A"),
    TmApp (TmVar ("x", TyArrow (TyTrue, TyVar "A")), TmTrue)
  )

  let or_comm = 
    TmAbs ("x", TyOr (TyVar "A", TyVar "B"),
      TmOrCase (TmVar ("x", TyOr (TyVar "A", TyVar "B")),
        ("a", TmRight (TmVar ("a", TyVar "A"), TyOr (TyVar "B", TyVar "A"))),
        ("b", TmLeft (TmVar ("b", TyVar "B"), TyOr (TyVar "B", TyVar "A")))
      )
    )

let negation_example =
  TmAbs ("x", TyAnd (TyVar "A", TyArrow (TyVar "A", TyFalse)),
    TmExFalso (
      TmApp (TmProj2 (TmVar ("x", TyAnd (TyVar "A", TyArrow (TyVar "A", TyFalse)))),
              TmProj1 (TmVar ("x", TyAnd (TyVar "A", TyArrow (TyVar "A", TyFalse))))),
      TyVar "B"
    )
  )




(* Part 1 Test *)
let test () =
  (* Test produit *)
  let term_prod = TmPair (TmVar ("x", TyVar "A"), TmVar ("y", TyVar "B")) in
  let ctx = [("x", TyVar "A"); ("y", TyVar "B")] in
  let inferred_prod_ty = infer_type ctx term_prod in
  assert (inferred_prod_ty = TyProd (TyVar "A", TyVar "B"));

  (* Test somme *)
  (*let term_sum = TmInl (TmVar ("x", TyVar "A"), TySum (TyVar "A", TyVar "B")) in 
  let inferred_sum_ty = infer_type ctx term_sum in
  assert (inferred_sum_ty = TySum (TyVar "A", TyVar "B")); *)

  (* Test unité *)
  let term_unit = TmUnit in
  let inferred_unit_ty = infer_type [] term_unit in
  assert (inferred_unit_ty = TyUnit);

  (* Test zéro *)
  let term_zero_case = TmZeroCase (TmVar ("z", TyZero)) in
  let inferred_zero_ty = infer_type [("z", TyZero)] term_zero_case in
  assert (inferred_zero_ty = TyZero);

  (* Test conjunction *)
  let term_and = TmAndIntro (TmVar ("x", TyVar "A"), TmVar ("y", TyVar "B")) in
  let inferred_and_ty = infer_type ctx term_and in
  assert (inferred_and_ty = TyAnd (TyVar "A", TyVar "B"));

  (* Test truth *)
  let inferred_truth_ty = infer_type [] tru_comm in
  assert (inferred_truth_ty = TyArrow (TyArrow (TyTrue, TyVar "A"), TyVar "A"));

  (* Test disjunction *)
  let inferred_or_ty = infer_type [] or_comm in
  assert (inferred_or_ty = TyArrow (TySum (TyVar "A", TyVar "B"), TySum (TyVar "B", TyVar "A")));

  (* Test falsity *)
  let inferred_neg_ty = infer_type [] negation_example in
  assert (inferred_neg_ty = TyArrow (TyAnd (TyVar "A", TyArrow (TyVar "A", TyFalse)), TyVar "B"))

(* You can run the test with let() = test () *)

(* 1.12 Parsing strings *)

let () =
  let l = [
    "A => B";
    "A ⇒ B";
    "A /\\ B";
    "A ∧ B";
    "T";
    "A \\/ B";
    "A ∨ B";
    "_";
    "not A";
    "¬ A";
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))
    ) l

let () =
  let l = [
    "t u v";
    "fun (x : A) -> t";
    "λ (x : A) → t";
    "(t , u)";
    "fst(t)";
    "snd(t)";
    "()";
    "case t of x -> u | y -> v";
    "left(t,B)";
    "right(A,t)";
    "absurd(t,A)"
  ]
  in
  List.iter
    (fun s ->
        Printf.printf
          "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))
    ) l

(* 2.1 String representation of contexts *)

let string_of_ctx (ctx : (string * ty) list) : string =
  "[" ^
  (ctx
   |> List.map (fun (var, ty) -> var ^ " : " ^ string_of_ty ty)
   |> String.concat ", ") ^
  "]"

(* 2.2 Sequents *)

type sequent = context * ty

let string_of_seq (ctx, ty) : string =
  string_of_ctx ctx ^ " ⊢ " ^ string_of_ty ty

(* 2.3 An interactive prover *)

let rec prove env a =
  print_endline (string_of_seq (env, a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" ->
     (match a with
      | TyArrow (a, b) ->
        if arg = "" then error "Please provide an argument for intro."
        else
          let x = arg in
          let t = prove ((x, a) :: env) b in
          TmAbs (x, a, t)
      | _ ->
        error "Don't know how to introduce this.")
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else t
  | "elim" ->
     let t = tm_of_string arg in
     let ty = infer_type env t in
     (match ty with
      | TyArrow (a, _) ->
        let u = prove env a in
        TmApp (t, u)
      | _ -> error "The given term is not of the form A -> B")
  | cmd -> error ("Unknown command: " ^ cmd)
  
let prove_from_file filename =
  let infile = open_in filename in
  try
    let a = input_line infile in
    let a = ty_of_string a in
    print_endline ("Verifying the proof for: " ^ string_of_ty a);
    let rec process_file env a =
      try
        let line = input_line infile in
        let cmd, arg =
          let n = try String.index line ' ' with Not_found -> String.length line in
          let c = String.sub line 0 n in
          let a = String.sub line n (String.length line - n) in
          let a = String.trim a in
          c, a
        in
        match cmd with
        | "intro" ->
          (match a with
           | TyArrow (a, b) ->
             let x = arg in
             process_file ((x, a) :: env) b
           | _ -> failwith "Intro rule applied to a non-arrow type")
        | "exact" ->
          let t = tm_of_string arg in
          if infer_type env t <> a then failwith "Exact: Not the right type."
          else print_endline "Exact step verified."
        | "elim" ->
          let t = tm_of_string arg in
          let ty = infer_type env t in
          (match ty with
           | TyArrow (a, _) ->
             let u = prove env a in
             let _ = TmApp (t, u) in
             print_endline "Elim step verified."
           | _ -> failwith "Elim: The given term is not of the form A -> B")
        | cmd -> failwith ("Unknown command in file: " ^ cmd)
      with End_of_file ->
        print_endline "Proof verification complete.";
    in
    process_file [] a;
    close_in infile;
    print_endline "The proof is correct."
  with e ->
    close_in_noerr infile;
    print_endline ("Error while verifying the proof: " ^ Printexc.to_string e)

let () =
  print_endline "Do you want to test a file or prove a formula? (type 'file' or 'formula')";
  let choice = input_line stdin in
  if choice = "file" then (
    print_endline "Enter the file name:";
    let filename = input_line stdin in
    prove_from_file filename
  ) else if choice = "formula" then (
    print_endline "Please enter the formula to prove:";
    let a = input_line stdin in
    let a = ty_of_string a in
    print_endline "Let's prove it.";
    let t = prove [] a in
    print_endline "done.";
    print_endline "Proof term is";
    print_endline (string_of_tm t);
    print_string "Typechecking... "; flush_all ();
    assert (infer_type [] t = a);
    print_endline "ok."
  ) else (
    print_endline "Unknown choice. Exiting."
  )
