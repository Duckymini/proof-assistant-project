%{
open Expr
%}

%token IMP AND OR TRUE FALSE NOT
%token FUN TO CASE OF
%token LPAR RPAR COLON COMMA BAR
%token FST SND LEFT RIGHT ABSURD
%token <string> IDENT
%token EOF

%right IMP
%right OR
%right AND
%nonassoc NOT

%start ty
%start tm
%type <Expr.ty> ty
%type <Expr.tm> tm
%%

/* A type */
ty:
  | IDENT        { TyVar $1 }
  | ty IMP ty    { TyArrow ($1, $3) }
  | ty AND ty    { TyAnd ($1, $3) }
  | ty OR ty     { TyOr ($1, $3) }
  | NOT ty       { TyArrow ($2, TyFalse) }
  | TRUE         { TyTrue }
  | FALSE        { TyFalse }
  | LPAR ty RPAR { $2 }

/* A term */
tm:
  | atm                                    { $1 }
  | FUN LPAR IDENT COLON ty RPAR TO tm     { TmAbs ($3, $5, $8) }
  | CASE tm OF IDENT TO tm BAR IDENT TO tm { TmCase ($2, ($4, $6), ($8, $10)) }

/* An application */
atm:
  | stm     { $1 }
  | atm stm { TmApp ($1, $2) }

/* A simple term */
stm:
  | IDENT                        { TmVar ($1, TyVar "default") }
  | LPAR tm RPAR                 { $2 }
  | FST stm                      { TmProj1 $2 }
  | SND stm                      { TmProj2 $2 }
  | LPAR RPAR                    { TmUnit }
  | LPAR tm COMMA tm RPAR        { TmPair ($2, $4) }
  | LEFT LPAR tm COMMA ty RPAR   { TmLeft ($3, $5) }
  | RIGHT LPAR tm COMMA ty RPAR  { TmRight ($3, $5) }
  | ABSURD LPAR tm COMMA ty RPAR { TmAbsurd ($3, $5) }
