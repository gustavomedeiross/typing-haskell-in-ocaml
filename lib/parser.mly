%{
open Infer

(* f a b c -> (((f a) b) c) *)
let rec make_application e = function
  | [] -> failwith "precondition violated"
  | [e'] -> Application (e, e')
  | e' :: es -> make_application (Application (e, e')) es
%}

%token <int> INT
%token <string> IDENT
%token TRUE
%token FALSE
%token FUN
%token ARROW
%token LPARENS
%token RPARENS
%token LET
%token IN
%token EQUALS
%token COLON
%token EOF
%token TINT
%token TBOOL

%start <Infer.expr> prog
%start <Infer.typ> typ

%%

let prog :=
  | e = expr; EOF; { e }

let typ :=
  | t = typ_expr; EOF; { t }

let expr :=
  | sub_expr
  | application
  | let_expr

let sub_expr ==
  | terminal
  | LPARENS; e=expr; RPARENS; { e }

let terminal ==
  | var = IDENT; { Var var }
  | i = INT; { Lit (LitInt i) }
  | boolean

let boolean ==
  | TRUE; { Lit (LitBool true) }
  | FALSE; { Lit (LitBool false) }

let let_expr ==
  (* | LET; name = IDENT; EQUALS; e1 = expr; IN; e2 = expr; { Let (name, e1, e2) } *)
  | LET; name = IDENT; EQUALS; e1 = expr; IN; e2 = expr; {
        let alt = ([], e1) in
        let binding = (name, [alt]) in
        let bind_group = ([], [[binding]]) in
        Let (bind_group, e2)
      }

(* TODO: we're not going to have lambda/abstractions for now *)
(* let abstraction ==
  | FUN; param = IDENT; COLON; t = typ_expr; ARROW; e = expr; { Abstraction (param, Some t, e) }
  | FUN; param = IDENT; ARROW; e = expr; { Abstraction (param, None, e) }
*)

let typ_expr :=
  | typ_terminal
  | typ_arrow
  | LPARENS; t = typ_expr; RPARENS; { t }

(* TODO: change it to IDENT with a initial type env *)
let typ_terminal ==
  | TINT; { t_int }
  | TBOOL; { t_bool }

let typ_arrow ==
  | t1 = typ_expr; ARROW; t2 = typ_expr; { TApp (t1, t2) }

let application :=
  | e = sub_expr; es = sub_expr+; { make_application e es }
