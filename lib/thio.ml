module Infer = Infer

let parse (s : string) : Infer.expr =
  let lexbuf = Lexing.from_string s in
  Parser.prog Lexer.read lexbuf

let typecheck str = 
  str
  |> parse
  |> Infer.ti_expr Infer.initial_class_env []
  |> Infer.run_ti

let rec type_to_string typ =
  let open Infer in
  match typ with
  | TVar (Tyvar (id, _kind)) -> id
  | TCon (Tycon (id, _kind)) -> id
  | TApp (t1, t2) -> (type_to_string t1) ^ " " ^ (type_to_string t2)
  | TGen n -> "TGen " ^ (Int.to_string n)

let pred_to_string (Infer.IsIn (id, typ)) =
  id ^ " " ^ (type_to_string typ)
  
let preds_to_string preds =
  let preds =
    preds
    |> List.map pred_to_string
    |> String.concat ", "
  in
  "(" ^ preds ^ ")"

let qual_type_to_string (preds, typ) =
  (preds_to_string preds) ^ " => " ^ (type_to_string typ)
    
