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

let kind_tyvar : tyvar -> kind = function
  | Tyvar (_v, k) -> k

let kind_tycon : tycon -> kind = function
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
let merge (s1 : subst) (s2 : subst) : (subst, type_err) result =
  let intersection = intersect equal_tyvar (List.map fst s1) (List.map fst s2) in
  let agree = List.for_all (fun v -> equal_typ (apply_typ s1 (TVar v)) (apply_typ s2 (TVar v))) intersection in
  if agree then Ok (s1 @ s2) else Error (TypeError "merge fails")

(* |- Unification and Matching *)

let var_bind (u : tyvar) (t : typ) : (subst, type_err) result =
  match t with
  | t when equal_typ (TVar u) t -> Ok null_subst
  | t when List.exists (fun v -> equal_tyvar v u) (ftv_typ t) -> Error (TypeError "occurs check fails")
  (* It should be kind-preserving *)
  | t when not (equal_kind (kind_tyvar u) (kind_typ t)) -> Error (TypeError "kinds do not match")
  | _ -> Ok (u +-> t)

let rec mgu (t1 : typ) (t2 : typ) : (subst, type_err) result =
  match t1, t2 with
  | TApp (l, r), TApp (l', r') ->
     let* s1 = mgu l l' in
     let* s2 = mgu r r' in
     Ok (s2 @@ s1)
  | TVar u, t -> var_bind u t
  | t, TVar u -> var_bind u t
  | TCon tc1, TCon tc2 when equal_tycon tc1 tc2 -> Ok null_subst
  | _ -> Error (TypeError "Types do not unify")

(*
   From "Typing Haskell In Haskell":

   In the following sections, we will also make use of an operation called matching that is closely related to unification.

   Given two types t1 and t2, the goal of matching is to find a substitution s such that apply s t1 = t2.
   Because the substitution is applied only to one type, this operation is often described as one-way matching.
   The calculation of matching substitutions is implemented by a function:
 *)
let rec match_ (t1 : typ) (t2 : typ) : (subst, type_err) result =
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

(* The expression `(Num a)` would be represented as `IsIn "Num" (TVar (Tyvar "a" Star))` *)
type pred = IsIn of id * typ
[@@deriving eq]

(*
  |- Represents a qualifier (or also quantifier I believe would also correct) for a type.

   - A function type, e.g.: "(Eq a, Eq b) => a -> b -> Bool"
   - A type class definition, e.g.: "class Applicativem => Monad m where"
   - A instance declaration, e.g.: "instance (Ord a, Ord b) => Ord (a, b) where"

   So in Haskell, basically every time we have a "=>".

   The pieces before the "=>" are the predicates, and the pieces after are generic - depends if it's a function, a type class, an instance declaration, etc. - that's why the type is generic.
 *)
type 'a qual = pred list * 'a
[@@deriving eq]

(*
   From "Typing Haskell In Haskell":

   For example, using the Qual and Pred datatypes, the type (Num a) => a -> Int can be represented by:
   [IsIn "Num" (TVar (Tyvar "a" Star))] :=> (TVar (Tyvar "a" Star) `fn` tInt)

 *)
type qual_type = typ qual

type qual_pred = pred qual

let apply_pred (s : subst) (IsIn (i, t)) : pred =
  IsIn (i, apply_typ s t)

let ftv_pred (IsIn (_i, t)) : tyvar list =
  ftv_typ t

let apply_qual (s : subst) (qual : 'a qual) (apply_fn : subst -> 'a -> 'a) : 'a qual =
  let (ps, a) = qual in
  (apply_list s ps apply_pred), (apply_fn s a)

let apply_qual_type (s : subst) (qual : qual_type) : qual_type =
  apply_qual s qual apply_typ

let apply_qual_pred (s : subst) (qual : qual_pred) : qual_pred =
  apply_qual s qual apply_pred

let ftv_qual ((ps, a) : 'a qual) (ftv_fn : 'a -> tyvar list) : tyvar list =
  union equal_tyvar (ftv_list ps ftv_pred) (ftv_fn a)

let ftv_qual_type (qual : qual_type) : tyvar list =
  ftv_qual qual ftv_typ

let ftv_qual_pred (qual : qual_pred) : tyvar list =
  ftv_qual qual ftv_pred

let lift f (IsIn (i, t)) (IsIn (i', t')) =
  if equal_id i i'
  then (f t t')
  else Error (TypeError "classes differ")

let mgu_pred (p1 : pred) (p2 : pred) : (subst, type_err) result =
  lift mgu p1 p2

let match_pred (p1 : pred) (p2 : pred) : (subst, type_err) result =
  lift match_ p1 p2

type inst = qual_pred

type typeclass = id list * inst list

module ClassEnv = Map.Make(String)

type class_env = { classes : typeclass ClassEnv.t;  defaults : typ list }

let classes (env : class_env) (id: id) : (typeclass, type_err) result =
  match ClassEnv.find_opt id (env.classes) with
  | Some tc -> Ok tc
  | None -> Error (TypeError "type class not found")

let super (env : class_env) (id : id) : (id list, type_err) result =
  classes env id |> Result.map fst

let super_exn env id =
  match super env id with
  | Ok x -> x
  | Error (TypeError e) -> failwith e

let insts (env : class_env) (id : id) : (inst list, type_err) result =
  Result.map snd (classes env id)

let insts_exn env id =
  match insts env id with
  | Ok x -> x
  | Error (TypeError e) -> failwith e

let defined = Result.is_ok

let modify (env : class_env) (id : id) (tc : typeclass) : class_env =
  let classes' = ClassEnv.add id tc env.classes in
  { classes = classes'; defaults = env.defaults }

let initial_class_env =
  {
    classes = ClassEnv.empty;
    defaults = [t_integer; t_double];
  }

(*
  |- Add a type class to the class_env

  On the statement "class (Eq a) => Ord a where"

  - Ord would be the "id" argument
  - (Eq a) would be the "superclasses" argument
 *)
let add_class (id : id) (superclasses : id list) (env : class_env) : (class_env, type_err) result =
  if defined (classes env id)
     then Error (TypeError "class already defined")
  else if not (List.for_all (fun super -> defined (classes env super)) superclasses)
     then Error (TypeError "superclass not defined")
  else Ok (modify env id (superclasses, []))

(*
  From "Typing Haskell In Haskell":

  This test covers simple cases where a program provides two instance declarations for the same type
  (e.g., two declarations for Eq Int),

  but it also covers cases where more interesting overlaps occur
  (e.g., between the predicates Eq [Int] and Eq [a], or between predicates Eq (a,Bool) and Eq (Int,b)).

  In each case, the existence of an overlap indicates the possibility of a semantic ambiguity,
  with two applicable instance declarations, and no clear reason to prefer one over the other.
  This is why Haskell treats such overlaps as an error.
 *)
let overlap (p : pred) (q : pred) : bool = defined (mgu_pred p q)

let instance_overlaps_with_existing_definition (instance : pred) (env : class_env) : bool =
  let IsIn(id, _typ) = instance in
  let existing_instances = insts_exn env id in
  existing_instances
  |> List.map snd
  |> List.exists (fun q -> overlap instance q) 

(*
  |- Adds a type class instance to the class_env

  On the statement "instance (Ord a, Ord b) => Ord (a, b) where"

  - (Ord a, Ord b) would be the "predicates" argument
  - Ord (a, b) would be the "instance" argument
 *)
let add_instance (predicates : pred list) (instance : pred) (env : class_env) : (class_env, type_err) result =
  let IsIn(id, _typ) = instance in
  let class_is_defined = defined (classes env id) in
  if not (class_is_defined)
  then Error (TypeError "no class for instance")
  else if (instance_overlaps_with_existing_definition instance env)
  then Error (TypeError "overlapping instance")
  else
    let existing_insts = insts_exn env id in
    let clazz = (super_exn env id, (predicates, instance) :: existing_insts) in
    Ok (modify env id clazz)

type env_transformer = class_env -> (class_env, type_err) result
  
let (<:>) (f : env_transformer) (g : env_transformer) (env : class_env) : (class_env, type_err) result =
  let* env' = f env in g env'

let add_core_classes : env_transformer =
  add_class "Eq" []
  <:> add_class "Ord" ["Eq"]
  <:> add_class "Show" []
  <:> add_class "Read" []
  <:> add_class "Bounded" []
  <:> add_class "Enum" []
  <:> add_class "Functor" []
  <:> add_class "Applicative" ["Functor"]
  <:> add_class "Monad" ["Applicative"]

let add_num_classes : env_transformer =
  add_class "Num" ["Eq"; "Show"]
  <:> add_class "Real" ["Num"; "Ord"]
  <:> add_class "Fractional" ["Num"]
  <:> add_class "Integral" ["Real"; "Enum"]
  <:> add_class "RealFrac" ["Real"; "Fractional"]
  <:> add_class "Floating" ["Fractional"]
  <:> add_class "RealFloat" ["RealFrac"; "Floating"]

let add_prelude_classes : env_transformer = add_core_classes <:> add_num_classes

let example_insts : env_transformer =
  add_instance [] (IsIn ("Ord", t_unit))
  (* instance Ord Char where *)
  <:> add_instance [] (IsIn ("Ord", t_char))
  <:> add_instance [] (IsIn ("Ord", t_int))
  (* instance (Ord a, Ord b) => Ord (a, b) where*)
  <:> add_instance [
          IsIn ("Ord", TVar (Tyvar ("a", Star)));
          IsIn ("Ord", TVar (Tyvar ("b", Star)))]
        (IsIn ("Ord", (pair (TVar (Tyvar ("a", Star)))
                            (TVar (Tyvar ("b", Star))))))

(*
  |- Returns a list of predicates informing which classes a given type is instance of, "flattened"

  e.g. Knowing that Eq is a superclass of Ord, if the type Int implements Ord

  input: IsIn ("Ord", t_int)
  output: [IsIn ("Ord", t_int), IsIn ("Eq", t_int)]
 *)
let rec by_super (class_env : class_env) (pred : pred) : pred list =
  let IsIn(clazz, typ) = pred in
  let super_classes = super_exn class_env clazz in
  let super_classes_flattened =
    super_classes
    |> List.map (fun clazz -> by_super class_env (IsIn (clazz,typ)))
    |> List.flatten
  in
  pred :: super_classes_flattened


(* TODO: understand and refactor *)
let by_instance (class_env : class_env) (pred : pred) : pred list option =
  let IsIn(i, t) = pred in
  let instances = insts_exn class_env i in
  let try_inst ((preds, head) : qual_pred) : pred list option =
    let maybe_subst = match_pred head pred |> Result.to_option in
    Option.map (fun subst -> List.map (apply_pred subst) preds) maybe_subst
  in
  List.map try_inst instances
  |> List.find (Option.is_some)

(*
   From "Typing Haskell In Haskell":

  Given a predicate p and a list of predicates ps, our goal is to determine whether p will hold whenever all of the predicates in ps are satisfied.
  In the special case where p = IsIn i t and ps = [], this amounts to determining whether t is an instance of the class i.

  TODO: understand and refactor
 *)
let rec entail (class_env : class_env) (preds: pred list) (head : pred) : bool =
  (* Is "head" implied directly by something in "preds"? *)
  List.exists (fun p ->
                let p_superclasses = by_super class_env p in
                List.mem head p_superclasses
    ) preds ||
    (* If that's not the case, is there an instance where "preds" satisfies all
      the preconditions of the instance? *)
    match by_instance class_env head with
        | None -> false
        | Some heads -> List.for_all (entail class_env preds) heads

