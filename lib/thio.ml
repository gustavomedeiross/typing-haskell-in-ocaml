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

let split_triple (lst : ('a * 'b * 'c) list) : 'a list * 'b list * 'c list =
  let reducer acc (a, b, c) =
    let (a', b', c')  = acc in
    (a :: a', b :: b', c :: c')
  in
  List.fold_left reducer ([], [], []) lst

type type_err = TypeError of string

type 'a or_type_err = ('a, type_err) result

let (let*) x f = Result.bind x f

let sequence_result (lst : ('a, 'b) result list) : ('a list, 'b) result =
  let rec loop lst acc =
    match lst with
    | [] -> Ok (List.rev acc)
    | Error e :: _xs -> Error e
    | Ok x :: xs -> loop xs (x :: acc)
  in
  loop lst []

let map_m_result f lst =
  lst
  |> List.map f
  |> sequence_result

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

let t_string = list t_char

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

let mgu_exn t1 t2 = mgu t1 t2 |> Result.get_ok

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
   - A type class definition, e.g.: "class Applicative m => Monad m where"
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
[@@deriving eq]

type qual_pred = pred qual
[@@deriving eq]

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
let rec by_super (class_env : class_env) (head : pred) : pred list =
  let IsIn(clazz, typ) = head in
  let super_classes = super_exn class_env clazz in
  let super_classes_flattened =
    super_classes
    |> List.map (fun clazz -> by_super class_env (IsIn (clazz,typ)))
    |> List.flatten
  in
  head :: super_classes_flattened


(* TODO: understand and refactor *)
let by_instance (class_env : class_env) (head : pred) : pred list option =
  let IsIn(i, _t) = head in
  let instances = insts_exn class_env i in
  let try_inst ((preds, head) : qual_pred) : pred list option =
    let maybe_subst = match_pred head head |> Result.to_option in
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


(*
  From "Typing Haskell In Haskell":

  [...] the syntax of Haskell requires class arguments to be of the form v t1 ... tn, where v is a type variable, and t1,...,tn are types (and n ³ 0).
  The following function allows us to determine whether a given predicate meets these restrictions:

  ---

  So basically this checks if a predicate in in the form of "Class var", e.g. "Num a"
 *)
let in_head_normal_form (IsIn (_, typ)) : bool =
  let rec hnf = function
    | TVar _ -> true
    | TCon _ -> false
    | TApp (t, _) -> hnf t
    | TGen _ -> failwith "TGen not implemented"
  in
  hnf typ


let rec to_head_normal_form (class_env : class_env) (pred : pred) : (pred list, type_err) Result.t =
  if in_head_normal_form pred then
    Result.ok([pred])
  else
    match by_instance class_env pred with
    | None -> Result.error (TypeError "context reduction")
    | Some ps -> to_head_normal_form_list class_env ps

(* TODO: refactor *)
and to_head_normal_form_list (class_env : class_env) (preds : pred list) : (pred list, type_err) result =
  let* pss = map_m_result (to_head_normal_form class_env) preds in
  pss
  |> List.concat
  |> Result.ok


(* |- Goes through a predicate list and removes entailed entries *)
let simplify (class_env : class_env) (preds : pred list) : pred list =
  let rec loop preds simplified_preds =
    match preds with
    | [] -> simplified_preds
    | p :: ps ->
       if entail class_env (simplified_preds @ ps) p
       then loop ps simplified_preds
       else loop ps (p :: simplified_preds)
  in
  loop preds []

(*
   From "Typing Haskell In Haskell":

   Now we can describe the particular form of context reduction used in Haskell as a combination of toHnfs and simplify.
   Specifically, we use toHnfs to reduce the list of predicates to head-normal form, and then simplify the result:
 *)
let reduce (class_env : class_env) (preds : pred list) : (pred list, type_err) result =
  preds
  |> to_head_normal_form_list class_env
  |> Result.map (simplify class_env)

(*
  From "Typing Haskell In Haskell":

  As a technical aside, we note that there is some redundancy in the definition of reduce.
  The simplify function is defined in terms of entail, which makes use of the information provided by both superclass and instance declarations.
  The predicates in qs, however, are guaranteed to be in head-normal form, and hence will not match instance declarations that satisfy the syntactic restrictions of Haskell.

  It follows that we could make do with a version of simplify that used only the following function in determining (superclass) entailments:
 *)
let sc_entail (class_env : class_env) (preds : pred list) (pred : pred) : bool =
  preds
  |> List.map (by_super class_env)
  |> List.exists (List.mem pred)

(* |- Type Schemes *)

type scheme = Forall of kind list * qual_type
[@@deriving eq]

let apply_scheme (subst : subst) (Forall (kinds, qual_type)) : scheme =
  Forall (kinds, (apply_qual_type subst qual_type))

let ftv_scheme (Forall (_, qual_type)) : tyvar list =
  ftv_qual_type qual_type

(* Type schemes are constructed by quantifying a qualified type qual_type with respect to a list of type variables tyvars: *)
let quantify (tyvars : tyvar list) (qual_type : qual_type) : scheme =
  let tyvars' =
    ftv_qual_type qual_type
    |> List.filter (fun v -> List.mem v tyvars)
  in
  let kinds = List.map kind_tyvar tyvars' in
  let t_gens = List.init (List.length tyvars') Fun.id |> List.map (fun x -> TGen x) in
  let subst = List.combine tyvars' t_gens in
  Forall (kinds, (apply_qual_type subst qual_type))


(* In practice, we sometimes need to convert a Type into a Scheme without adding any qualifying predicates or quantified variables.
   For this special case, we can use the following function instead of quantify: *)
let to_scheme (typ : typ) : scheme =
  Forall ([], ([], typ))

(* |- Assumptions *)

(* Assumptions about the type of a variable are represented by values of the Assump datatype, each of which pairs a variable name with a type scheme: *)
type assump = id * scheme

let apply_assump (subst : subst) (id, scheme) : assump =
  id, (apply_scheme subst scheme)

let ftv_assump (_, scheme) : tyvar list =
  ftv_scheme scheme

let rec find id (assumptions : assump list) : scheme or_type_err =
  match assumptions with
  | [] -> Error (TypeError ("unbound identifier " ^ id))
  | (id', scheme) :: assumptions' ->
     if id == id' then
       Ok scheme
     else
       find id assumptions'

let find_exn id assumps = find id assumps |> Result.get_ok

(* |- Type Inference Monad *)

type 'a ti = TI of (subst -> int -> (subst * int * 'a))

let return_ti x = TI (fun s n -> (s, n, x))

let bind_ti (TI f) g = TI (fun s n ->
                      let (s', m, x) =  f s n in
                      let TI gx = g x in
                      gx s' m)

let (let+) x f = bind_ti x f

let run_ti (TI f) =
  let (_s, _n, x) = f null_subst 0 in
  x

let rec sequence_ti lst =
  match lst with
  | [] -> return_ti []
  | x :: xs ->
      let+ y = x in
      let+ ys = sequence_ti xs in
      y :: ys |> return_ti

let map_m_ti f lst =
  lst |> List.map f |> sequence_ti

let get_subst = TI (fun s n -> (s, n, s))

let extend_subst (subst : subst) : unit ti =
  TI (fun s n -> (subst @@ s, n, ()))

let unify (t1 : typ) (t2 : typ) : unit ti =
  let+ subst = get_subst in
  let u = mgu_exn (apply_typ subst t1) (apply_typ subst t2) in
  extend_subst u

let new_tvar (kind : kind) : typ ti =
  TI (fun s n ->
      let var = Tyvar ((enum_id n), kind) in
      (s, n+1, TVar var))

let rec inst_type ts = function
  | TApp (l, r) -> TApp (inst_type ts l, inst_type ts r)
  | TGen n -> List.nth ts n
  | t -> t

let inst_pred ts (IsIn (c, t)) =
  IsIn (c, (inst_type ts t))

let inst_pred_list ts preds =
  List.map (fun p -> inst_pred ts p) preds

let inst_qual_type (ts : typ list) ((ps, t) : qual_type) =
  (inst_pred_list ts ps, inst_type ts t)

let fresh_inst (Forall (kinds, qual_type)) : qual_type ti =
  let+ ts = map_m_ti new_tvar kinds in
  return_ti (inst_qual_type ts qual_type)

(* |- Type Inference *)


(* 'e is an expression and 't is a corresponding type *)
type ('e, 't) infer  = class_env -> assump list -> 'e -> (pred list * 't) ti

(* |-- Type inference for literals *)

type literal =
  | LitInt of int
  | LitChar of char
  | LitRat of float
  | LitStr of string

let ti_lit : literal -> (pred list * 't) ti = function
  | LitChar _ -> return_ti ([], t_char)
  (* Integer literals must be instances of the "Num" class *)
  | LitInt _ ->
     let+ v = new_tvar Star in
     return_ti ([IsIn ("Num", v)], v)
  | LitStr _ -> return_ti ([], t_string)
  (* Rational literals must be instances of the "Fractional" class *)
  | LitRat _ ->
     let+ v = new_tvar Star in
     return_ti ([IsIn ("Fractional", v)], v)

(* |-- Type inference for patterns *)

(* Patterns are used to inspect and deconstruct data values in lambda abstractions, function and pattern bindings, list comprehensions, do notation, and case expressions. *)
type pattern =
  (* matches any value and binds the result to the variable i *)
  | PVar of id
  (* corresponding to an underscore _ in Haskell syntax, matches any value, but does not bind any variables *)
  | PWildcard
  (* "as-pattern": written using i@pat, binds the variable i to any value that matches the pattern pat,
     while also binding any variables that appear in pat *)
  | PAs of id * pattern
  (* matches only the particular value denoted by the literal l *)
  | PLit of literal
  (* is an (n+k) pattern, which matches any positive integral value m that is greater than or equal to k, and binds the variable i to the difference (m-k). *)
  | PNpk of id * int
  (* matches only values that were built using the constructor function a with a sequence of arguments that matches pats.
     We use values a of type Assump to represent constructor functions; all that we really need for typechecking is the type, although the name is useful for debugging.
     A full implementation would store additional details, such as arity, and use this to check that constructor functions in patterns are always fully applied. *)
  | PCon of assump * (pattern list)

(* Type inference for patterns has two goals: To calculate a type for each bound variable, and to determine what type of values the whole pattern might match. *)
let rec ti_pattern : pattern -> (pred list * assump list * typ) ti = function
  | PVar id ->
     let+ v = new_tvar Star in
     return_ti ([], [(id, to_scheme v)], v)
  | PWildcard ->
     let+ v = new_tvar Star in
     return_ti ([], [], v)
  | PAs (id, pat) ->
     let+ (preds, assumps, t) = ti_pattern pat in
     return_ti (preds, (id, to_scheme t) :: assumps, t)
  | PLit lit ->
     let+ (preds, t) = ti_lit lit in
     return_ti (preds, [], t)
  | PNpk (id, _k) ->
      let+ t = new_tvar Star in
      return_ti ([IsIn ("Integral", t)], [(id, to_scheme t)], t)

  (*
    The case for constructed patterns is slightly more complex:
    
    First we use the ti_patterns function, to calculate types ts for each subpattern in pats together with corresponding lists of assumptions in as and predicates in ps.
    Next, we generate a new type variable typ' that will be used to capture the (as yet unknown) type of the whole pattern.
    From this information, we would expect the constructor function at the head of the pattern to have type foldr fn t' ts.
    We can check that this is possible by instantiating the known type sc of the constructor and unifying.
   *)

  | PCon (assump, patterns) ->
     let (_id, scheme) = assump in
     let+ (preds, assumps, types) = ti_patterns patterns in
     let+ typ' = new_tvar Star in
     let+ qualifiers, typ = fresh_inst scheme in
     let+ () = unify typ (List.fold_right fn types typ') in
     return_ti (preds @ qualifiers, assumps, typ')


and ti_patterns (pats : pattern list) : (pred list * assump list * typ list) ti =
  let+ psasts = map_m_ti ti_pattern pats in
  let (preds, assumps, types) = split_triple psasts in
  return_ti (List.concat preds, List.concat assumps, types)

type expr =
  | Var of id
  | Lit of literal
  (* The Const constructor is used to deal with named constants, such as the constructor or selector functions associated with a
     particular datatype or the member functions that are associated with a particular class.
     We use values of type Assump to supply a name and type scheme, which is all the information that we need for the purposes of type inference. *)
  | Const of assump
  | Application of expr * expr
  (* TODO: | Let of bind_group * expr *)

let rec ti_expr (class_env : class_env) (assumps : assump list) (expr : expr) : (pred list * typ) ti =
  match expr with
  | Var id ->
     let scheme = find_exn id assumps in
     let+ (preds, typ) = fresh_inst scheme in
     return_ti (preds, typ)
  | Const (_id, scheme) ->
      let+ (preds, typ) = fresh_inst scheme in
      return_ti (preds, typ)
  | Lit lit -> ti_lit lit
  | Application (expr', func) ->
     let+ (expr_ps, expr_typ) = ti_expr class_env assumps expr' in
     let+ (func_ps, func_typ) = ti_expr class_env assumps func in
     let+ t = new_tvar Star in
     let+ () = unify (fn func_typ t) expr_typ in
     return_ti (expr_ps @ func_ps, t)
(* TODO: bindgroup *)

(* |-- Type inference for alternatives *)

(* An alternative specifies the left and right hand sides of a function definition.
   With a more complete syntax for Expr, values of type Alt might also be used in the representation of lambda and case expressions. *)
type alt = (pattern list) * expr

let ti_alt (class_env : class_env) (assumps : assump list) (pats, e : alt) : (pred list * typ) ti =
  let+ (ps, assumps', ts) = ti_patterns pats in
  let+ (qs, t) = ti_expr class_env (assumps' @ assumps) e in
  return_ti (ps @ qs, List.fold_right fn ts t)

