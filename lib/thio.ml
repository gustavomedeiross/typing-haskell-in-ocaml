(* |- Helpers *)
let rec union eq xs = function
  | y :: ys when List.exists (fun x -> eq x y) xs -> union eq xs ys
  | y :: ys -> union eq (y :: xs) ys
  | [] -> xs

let rec intersect eq xs ys =
  match xs with
  | x :: xs when List.exists (fun y -> eq x y) ys -> (x :: intersect eq xs ys)
  | _ :: xs -> intersect eq xs ys
  | [] -> []

let remove_duplicates eq lst =
  List.fold_left (fun acc x ->
      let exists = List.exists (fun v -> eq v x) acc in
      if exists then
        acc
      else
        x :: acc
    ) [] lst
  |> List.rev

type type_err = TypeError of string

let (let*) x f = Result.bind x f

(* |- Types *)

type id = string
[@@deriving eq]

let enum_id (n : int) : id = "v" ^ string_of_int n

type kind = Star | Kfun of kind * kind
[@@deriving eq]

type tyvar = Tyvar of id * kind
[@@deriving eq]

type tycon = Tycon of id * kind
[@@deriving eq]

type typ =
  | TVar of tyvar
  | TCon of tycon
  | TApp of typ * typ
  (* TODO: change for something else instead of int *)
  | TGen of int
[@@deriving eq]

let t_unit = TCon (Tycon ("()", Star))
let t_char = TCon (Tycon ("Char", Star))
let t_int = TCon (Tycon ("Int", Star))
let t_integer = TCon (Tycon ("Integer", Star))
let t_float = TCon (Tycon ("Float", Star))
let t_double = TCon (Tycon ("Double", Star))

let t_list = TCon (Tycon ("[]", Kfun (Star, Star)))
let t_arrow = TCon (Tycon ("(->)", Kfun (Star, (Kfun (Star, Star)))))
let t_tuple2 = TCon (Tycon ("(,)", Kfun (Star, (Kfun (Star, Star)))))

(* Helper functions *)
let fn t1 t2 = TApp (TApp (t_arrow, t1), t2)
let list typ = TApp (t_list, typ)
let pair t1 t2 = TApp (TApp (t_tuple2, t1), t2)

(* |- Kinds *)

let rec kind_tyvar : tyvar -> kind = function
  | Tyvar (_v, k) -> k

let rec kind_tycon : tycon -> kind = function
  | Tycon (_c, k) -> k

(* TODO: fix TGen *)
let rec kind_typ : typ -> kind = function
  | TVar u -> kind_tyvar u
  | TCon c -> kind_tycon c
  | TGen _ -> failwith "function kind: TGen not implemented"
  | TApp (t, _) ->
     match kind_typ t with
     | Kfun (_, k) -> k
     | Star -> failwith "Type is not well-formed"

(* |- Substitutions *)
     
type subst = (tyvar * typ) list

let null_subst : subst = []

(* TODO give a name *)
let (+->) (u : tyvar) (t : typ) : subst = [(u, t)]

let apply_list (s : subst) (lst : 'a list) (apply_fn : subst -> 'a -> 'a) : 'a list =
  List.map (fun x -> apply_fn s x) lst

let ftv_list (lst : 'a list) (ftv_fn : 'a -> tyvar list) : tyvar list =
  lst |> List.concat_map ftv_fn |> remove_duplicates equal_tyvar

let rec apply_typ (s : subst) (typ : typ) : typ =
  match typ with
  | TVar u -> (
     match List.assoc_opt u s with
    | Some t -> t
    | None -> TVar u)
  | TApp (l, r) -> TApp (apply_typ s l, apply_typ s r)
  | t -> t

let rec ftv_typ : typ -> tyvar list = function
  | TVar u -> [u]
  (* TODO fix *)
  | TApp (l, r) -> union equal_tyvar (ftv_typ l) (ftv_typ r)
  | _ -> []

(* TODO give a name *)
let (@@) (s1 : subst) (s2 : subst) : subst =
  let s2 = List.map (fun (u, t) -> u, apply_typ s1 t) s2 in
  s1 @ s2

(* TODO: I still don't understand why this function is required instead of @@ *)
let merge (s1 : subst) (s2 : subst) : (subst, type_err) Result.t =
  let intersection = intersect equal_tyvar (List.map fst s1) (List.map fst s2) in
  let agree = List.for_all (fun v -> equal_typ (apply_typ s1 (TVar v)) (apply_typ s2 (TVar v))) intersection in
  if agree then Ok (s1 @ s2) else Error (TypeError "merge fails")

(* |- Unification and Matching *)

let var_bind (u : tyvar) (t : typ) : (subst, type_err) Result.t =
  match t with
  | t when equal_typ (TVar u) t -> Ok null_subst
  | t when List.exists (fun v -> equal_tyvar v u) (ftv_typ t) -> Error (TypeError "occurs check fails")
  (* It should be kind-preserving *)
  | t when not (equal_kind (kind_tyvar u) (kind_typ t)) -> Error (TypeError "kinds do not match")
  | _ -> Ok (u +-> t)

let rec mgu (t1 : typ) (t2 : typ) : (subst, type_err) Result.t =
  match t1, t2 with
  | TApp (l, r), TApp (l', r') ->
     let* s1 = mgu l l' in
     let* s2 = mgu r r' in
     Ok (s2 @@ s1)
  | TVar u, t -> var_bind u t
  | t, TVar u -> var_bind u t
  | TCon tc1, TCon tc2 when equal_tycon tc1 tc2 -> Ok null_subst
  | _ -> Error (TypeError "Types do not unify")

(* TODO: I still don't understand why this function is required *)
let rec match_ (t1 : typ) (t2 : typ) : (subst, type_err) Result.t =
  match t1, t2 with
  | TApp (l, r), TApp (l', r') ->
     let* sl = match_ l l' in
     let* sr = match_ r r' in
     merge sl sr
  (* It should be kind-preserving *)
  | TVar u, t when equal_kind (kind_tyvar u) (kind_typ t) -> Ok (u +-> t)
  | TCon tc1, TCon tc2 when equal_tycon tc1 tc2 -> Ok null_subst
  | _ -> Error (TypeError "types do not match")

(* |- Type Classes, Predicates and Qualified Types *)

type pred = IsIn of id * typ
[@@deriving eq]

type qual = pred list * typ
[@@deriving eq]

let apply_pred (s : subst) (IsIn (i, t)) : pred =
  IsIn (i, apply_typ s t)

let ftv_pred (IsIn (_i, t)) : tyvar list =
  ftv_typ t

let apply_qual (s : subst) (qual : qual) : qual =
  let (ps, typ) = qual in
  (apply_list s ps apply_pred), (apply_typ s typ)

let ftv_qual ((ps, t) : qual) : tyvar list =
  union equal_tyvar (ftv_list ps ftv_pred) (ftv_typ t)

let lift f (IsIn (i, t)) (IsIn (i', t')) =
  if equal_id i i'
  then (f t t')
  else Error (TypeError "classes differ")

let mgu_pred (p1 : pred) (p2 : pred) : (subst, type_err) result =
  lift mgu p1 p2

let match_pred (p1 : pred) (p2 : pred) : (subst, type_err) result =
  lift match_ p1 p2
