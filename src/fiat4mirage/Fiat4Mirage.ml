type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| y :: l' -> Pervasives.succ (length l')

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

(** val id : 'a1 -> 'a1 **)

let id x =
  x

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val plus : int -> int -> int **)

let rec plus = (+)

(** val mult : int -> int -> int **)

let rec mult = ( * )

(** val minus : int -> int -> int **)

let rec minus = fun n m -> Pervasives.max 0 (n-m)

(** val nat_iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n0 f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    x)
    (fun n' ->
    f (nat_iter n' f x))
    n0

(** val le_gt_dec : int -> int -> bool **)

let le_gt_dec n0 m =
  (<=) n0 m

(** val le_dec : int -> int -> bool **)

let le_dec n0 m =
  le_gt_dec n0 m

(** val lt_dec : int -> int -> bool **)

let lt_dec n0 m =
  le_dec (Pervasives.succ n0) m

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> int **)
  
  let rec size_nat = function
  | XI p0 -> Pervasives.succ (size_nat p0)
  | XO p0 -> Pervasives.succ (size_nat p0)
  | XH -> Pervasives.succ 0
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step : (positive -> positive) -> (positive -> positive) -> (positive*mask) -> positive*mask **)
  
  let sqrtrem_step f g = function
  | s,y ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in let r' = g (f r) in if leb s' r' then (XI s),(sub_mask r' s') else (XO s),(IsPos r')
     | _ -> (XO s),(sub_mask (g (f XH)) (XO (XO XH))))
  
  (** val sqrtrem : positive -> positive*mask **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> XH,(IsPos (XO XH)))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> XH,(IsPos XH))
  | XH -> XH,IsNul
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    let x,y = sqrtrem p in x
  
  (** val gcdn : int -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> a
            | Lt -> gcdn n1 (sub b' a') a
            | Gt -> gcdn n1 (sub a' b') b)
         | XO b0 -> gcdn n1 a b0
         | XH -> XH)
      | XO a0 ->
        (match b with
         | XI p -> gcdn n1 a0 b
         | XO b0 -> XO (gcdn n1 a0 b0)
         | XH -> XH)
      | XH -> XH)
      n0
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn : int -> positive -> positive -> positive*(positive*positive) **)
  
  let rec ggcdn n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH,(a,b))
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> a,(XH,XH)
            | Lt -> let g,p = ggcdn n1 (sub b' a') a in let ba,aa = p in g,(aa,(add aa (XO ba)))
            | Gt -> let g,p = ggcdn n1 (sub a' b') b in let ab,bb = p in g,((add bb (XO ab)),bb))
         | XO b0 -> let g,p = ggcdn n1 a b0 in let aa,bb = p in g,(aa,(XO bb))
         | XH -> XH,(a,XH))
      | XO a0 ->
        (match b with
         | XI p -> let g,p0 = ggcdn n1 a0 b in let aa,bb = p0 in g,((XO aa),bb)
         | XO b0 -> let g,p = ggcdn n1 a0 b0 in (XO g),p
         | XH -> XH,(a,XH))
      | XH -> XH,(XH,b))
      n0
  
  (** val ggcd : positive -> positive -> positive*(positive*positive) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> int -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> int -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> int -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         true)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XO p0 ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         false)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XH ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         true)
         (fun n1 ->
         false)
         n0)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> int **)
  
  let to_nat x =
    iter_op plus x (Pervasives.succ 0)
  
  (** val of_nat : int -> positive **)
  
  let rec of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        XH)
        (fun n1 ->
        succ (of_nat x))
        x)
      n0
  
  (** val of_succ_nat : int -> positive **)
  
  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun x ->
      succ (of_succ_nat x))
      n0
 end

module Coq_Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> int **)
  
  let rec size_nat = function
  | XI p0 -> Pervasives.succ (size_nat p0)
  | XO p0 -> Pervasives.succ (size_nat p0)
  | XH -> Pervasives.succ 0
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step : (positive -> positive) -> (positive -> positive) -> (positive*mask) -> positive*mask **)
  
  let sqrtrem_step f g = function
  | s,y ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in let r' = g (f r) in if leb s' r' then (XI s),(sub_mask r' s') else (XO s),(IsPos r')
     | _ -> (XO s),(sub_mask (g (f XH)) (XO (XO XH))))
  
  (** val sqrtrem : positive -> positive*mask **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> XH,(IsPos (XO XH)))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> XH,(IsPos XH))
  | XH -> XH,IsNul
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    let x,y = sqrtrem p in x
  
  (** val gcdn : int -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> a
            | Lt -> gcdn n1 (sub b' a') a
            | Gt -> gcdn n1 (sub a' b') b)
         | XO b0 -> gcdn n1 a b0
         | XH -> XH)
      | XO a0 ->
        (match b with
         | XI p -> gcdn n1 a0 b
         | XO b0 -> XO (gcdn n1 a0 b0)
         | XH -> XH)
      | XH -> XH)
      n0
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn : int -> positive -> positive -> positive*(positive*positive) **)
  
  let rec ggcdn n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH,(a,b))
      (fun n1 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> a,(XH,XH)
            | Lt -> let g,p = ggcdn n1 (sub b' a') a in let ba,aa = p in g,(aa,(add aa (XO ba)))
            | Gt -> let g,p = ggcdn n1 (sub a' b') b in let ab,bb = p in g,((add bb (XO ab)),bb))
         | XO b0 -> let g,p = ggcdn n1 a b0 in let aa,bb = p in g,(aa,(XO bb))
         | XH -> XH,(a,XH))
      | XO a0 ->
        (match b with
         | XI p -> let g,p0 = ggcdn n1 a0 b in let aa,bb = p0 in g,((XO aa),bb)
         | XO b0 -> let g,p = ggcdn n1 a0 b0 in (XO g),p
         | XH -> XH,(a,XH))
      | XH -> XH,(XH,b))
      n0
  
  (** val ggcd : positive -> positive -> positive*(positive*positive) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> int -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> int -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> int -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         true)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XO p0 ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         false)
         (fun n' ->
         testbit_nat p0 n')
         n0)
    | XH ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         true)
         (fun n1 ->
         false)
         n0)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> int **)
  
  let to_nat x =
    iter_op plus x (Pervasives.succ 0)
  
  (** val of_nat : int -> positive **)
  
  let rec of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        XH)
        (fun n1 ->
        succ (of_nat x))
        x)
      n0
  
  (** val of_succ_nat : int -> positive **)
  
  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      XH)
      (fun x ->
      succ (of_succ_nat x))
      n0
  
  (** val eq_dec : positive -> positive -> bool **)
  
  let rec eq_dec p y0 =
    match p with
    | XI p0 ->
      (match y0 with
       | XI p1 -> eq_dec p0 p1
       | _ -> false)
    | XO p0 ->
      (match y0 with
       | XO p1 -> eq_dec p0 p1
       | _ -> false)
    | XH ->
      (match y0 with
       | XH -> true
       | _ -> false)
  
  (** val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let rec peano_rect a f p =
    let f2 = peano_rect (f XH a) (fun p0 x -> f (succ (XO p0)) (f (XO p0) x)) in
    (match p with
     | XI q -> f (XO q) (f2 q)
     | XO q -> f2 q
     | XH -> a)
  
  (** val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  (** val coq_PeanoView_rect :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rect f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rect f f0 p1 p2)
  
  (** val coq_PeanoView_rec :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rec f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rec f f0 p1 p2)
  
  (** val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xO p = function
  | PeanoOne -> PeanoSucc (XH, PeanoOne)
  | PeanoSucc (p0, q0) -> PeanoSucc ((succ (XO p0)), (PeanoSucc ((XO p0), (peanoView_xO p0 q0))))
  
  (** val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xI p = function
  | PeanoOne -> PeanoSucc ((succ XH), (PeanoSucc (XH, PeanoOne)))
  | PeanoSucc (p0, q0) -> PeanoSucc ((succ (XI p0)), (PeanoSucc ((XI p0), (peanoView_xI p0 q0))))
  
  (** val peanoView : positive -> coq_PeanoView **)
  
  let rec peanoView = function
  | XI p0 -> peanoView_xI p0 (peanoView p0)
  | XO p0 -> peanoView_xO p0 (peanoView p0)
  | XH -> PeanoOne
  
  (** val coq_PeanoView_iter : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_iter a f p = function
  | PeanoOne -> a
  | PeanoSucc (p0, q0) -> f p0 (coq_PeanoView_iter a f p0 q0)
  
  (** val eqb_spec : positive -> positive -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val switch_Eq : comparison -> comparison -> comparison **)
  
  let switch_Eq c = function
  | Eq -> c
  | x -> x
  
  (** val mask2cmp : mask -> comparison **)
  
  let mask2cmp = function
  | IsNul -> Eq
  | IsPos p0 -> Gt
  | IsNeg -> Lt
  
  (** val leb_spec0 : positive -> positive -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : positive -> positive -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : positive -> positive -> bool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : positive -> positive -> bool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : positive -> positive -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : positive -> positive -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module N = 
 struct 
  type t = n
  
  (** val zero : n **)
  
  let zero =
    N0
  
  (** val one : n **)
  
  let one =
    Npos XH
  
  (** val two : n **)
  
  let two =
    Npos (XO XH)
  
  (** val succ_double : n -> n **)
  
  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val double : n -> n **)
  
  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val succ : n -> n **)
  
  let succ = function
  | N0 -> Npos XH
  | Npos p -> Npos (Coq_Pos.succ p)
  
  (** val pred : n -> n **)
  
  let pred = function
  | N0 -> N0
  | Npos p -> Coq_Pos.pred_N p
  
  (** val succ_pos : n -> positive **)
  
  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p
  
  (** val add : n -> n -> n **)
  
  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.add p q))
  
  (** val sub : n -> n -> n **)
  
  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))
  
  (** val mul : n -> n -> n **)
  
  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Npos (Coq_Pos.mul p q))
  
  (** val compare : n -> n -> comparison **)
  
  let compare n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> Eq
       | Npos m' -> Lt)
    | Npos n' ->
      (match m with
       | N0 -> Gt
       | Npos m' -> Coq_Pos.compare n' m')
  
  (** val eqb : n -> n -> bool **)
  
  let rec eqb n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos p ->
      (match m with
       | N0 -> false
       | Npos q -> Coq_Pos.eqb p q)
  
  (** val leb : n -> n -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : n -> n -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val min : n -> n -> n **)
  
  let min n0 n' =
    match compare n0 n' with
    | Gt -> n'
    | _ -> n0
  
  (** val max : n -> n -> n **)
  
  let max n0 n' =
    match compare n0 n' with
    | Gt -> n0
    | _ -> n'
  
  (** val div2 : n -> n **)
  
  let div2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos p
     | XO p -> Npos p
     | XH -> N0)
  
  (** val even : n -> bool **)
  
  let even = function
  | N0 -> true
  | Npos p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  
  (** val odd : n -> bool **)
  
  let odd n0 =
    negb (even n0)
  
  (** val pow : n -> n -> n **)
  
  let pow n0 = function
  | N0 -> Npos XH
  | Npos p0 ->
    (match n0 with
     | N0 -> N0
     | Npos q -> Npos (Coq_Pos.pow q p0))
  
  (** val square : n -> n **)
  
  let square = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.square p)
  
  (** val log2 : n -> n **)
  
  let log2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos (Coq_Pos.size p)
     | XO p -> Npos (Coq_Pos.size p)
     | XH -> N0)
  
  (** val size : n -> n **)
  
  let size = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.size p)
  
  (** val size_nat : n -> int **)
  
  let size_nat = function
  | N0 -> 0
  | Npos p -> Coq_Pos.size_nat p
  
  (** val pos_div_eucl : positive -> n -> n*n **)
  
  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let q,r = pos_div_eucl a' b in
      let r' = succ_double r in if leb b r' then (succ_double q),(sub r' b) else (double q),r'
    | XO a' ->
      let q,r = pos_div_eucl a' b in
      let r' = double r in if leb b r' then (succ_double q),(sub r' b) else (double q),r'
    | XH ->
      (match b with
       | N0 -> N0,(Npos XH)
       | Npos p ->
         (match p with
          | XH -> (Npos XH),N0
          | _ -> N0,(Npos XH)))
  
  (** val div_eucl : n -> n -> n*n **)
  
  let div_eucl a b =
    match a with
    | N0 -> N0,N0
    | Npos na ->
      (match b with
       | N0 -> N0,a
       | Npos p -> pos_div_eucl na b)
  
  (** val div : n -> n -> n **)
  
  let div a b =
    let x,y = div_eucl a b in x
  
  (** val modulo : n -> n -> n **)
  
  let modulo a b =
    let x,y = div_eucl a b in y
  
  (** val gcd : n -> n -> n **)
  
  let gcd a b =
    match a with
    | N0 -> b
    | Npos p ->
      (match b with
       | N0 -> a
       | Npos q -> Npos (Coq_Pos.gcd p q))
  
  (** val ggcd : n -> n -> n*(n*n) **)
  
  let ggcd a b =
    match a with
    | N0 -> b,(N0,(Npos XH))
    | Npos p ->
      (match b with
       | N0 -> a,((Npos XH),N0)
       | Npos q -> let g,p0 = Coq_Pos.ggcd p q in let aa,bb = p0 in (Npos g),((Npos aa),(Npos bb)))
  
  (** val sqrtrem : n -> n*n **)
  
  let sqrtrem = function
  | N0 -> N0,N0
  | Npos p ->
    let s,m = Coq_Pos.sqrtrem p in
    (match m with
     | Coq_Pos.IsPos r -> (Npos s),(Npos r)
     | _ -> (Npos s),N0)
  
  (** val sqrt : n -> n **)
  
  let sqrt = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.sqrt p)
  
  (** val coq_lor : n -> n -> n **)
  
  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))
  
  (** val coq_land : n -> n -> n **)
  
  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Coq_Pos.coq_land p q)
  
  (** val ldiff : n -> n -> n **)
  
  let rec ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.ldiff p q)
  
  (** val coq_lxor : n -> n -> n **)
  
  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.coq_lxor p q)
  
  (** val shiftl_nat : n -> int -> n **)
  
  let shiftl_nat a n0 =
    nat_iter n0 double a
  
  (** val shiftr_nat : n -> int -> n **)
  
  let shiftr_nat a n0 =
    nat_iter n0 div2 a
  
  (** val shiftl : n -> n -> n **)
  
  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)
  
  (** val shiftr : n -> n -> n **)
  
  let shiftr a = function
  | N0 -> a
  | Npos p -> Coq_Pos.iter p div2 a
  
  (** val testbit_nat : n -> int -> bool **)
  
  let testbit_nat = function
  | N0 -> (fun x -> false)
  | Npos p -> Coq_Pos.testbit_nat p
  
  (** val testbit : n -> n -> bool **)
  
  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0
  
  (** val to_nat : n -> int **)
  
  let to_nat = function
  | N0 -> 0
  | Npos p -> Coq_Pos.to_nat p
  
  (** val of_nat : int -> n **)
  
  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      N0)
      (fun n' -> Npos
      (Coq_Pos.of_succ_nat n'))
      n0
  
  (** val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n0 f x =
    match n0 with
    | N0 -> x
    | Npos p -> Coq_Pos.iter p f x
  
  (** val eq_dec : n -> n -> bool **)
  
  let eq_dec n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos x ->
      (match m with
       | N0 -> false
       | Npos p0 -> Coq_Pos.eq_dec x p0)
  
  (** val discr : n -> positive option **)
  
  let discr = function
  | N0 -> None
  | Npos p -> Some p
  
  (** val binary_rect : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rect f0 f2 fS2 n0 =
    let f2' = fun p -> f2 (Npos p) in
    let fS2' = fun p -> fS2 (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p ->
       let rec f = function
       | XI p1 -> fS2' p1 (f p1)
       | XO p1 -> f2' p1 (f p1)
       | XH -> fS2 N0 f0
       in f p)
  
  (** val binary_rec : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rect f0 f n0 =
    let f' = fun p -> f (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p -> Coq_Pos.peano_rect (f N0 f0) f' p)
  
  (** val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 : n -> n -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : n -> n -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let recursion x =
    peano_rect x
  
  module Private_OrderTac = 
   struct 
    module IsTotal = 
     struct 
      
     end
    
    module Tac = 
     struct 
      
     end
   end
  
  module Private_NZPow = 
   struct 
    
   end
  
  module Private_NZSqrt = 
   struct 
    
   end
  
  (** val sqrt_up : n -> n **)
  
  let sqrt_up a =
    match compare N0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> N0
  
  (** val log2_up : n -> n **)
  
  let log2_up a =
    match compare (Npos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> N0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm : n -> n -> n **)
  
  let lcm a b =
    mul a (div b (gcd a b))
  
  (** val eqb_spec : n -> n -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2n : bool -> n **)
  
  let b2n = function
  | true -> Npos XH
  | false -> N0
  
  (** val setbit : n -> n -> n **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Npos XH) n0)
  
  (** val clearbit : n -> n -> n **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Npos XH) n0)
  
  (** val ones : n -> n **)
  
  let ones n0 =
    pred (shiftl (Npos XH) n0)
  
  (** val lnot : n -> n -> n **)
  
  let lnot a n0 =
    coq_lxor a (ones n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong : n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case : n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : n -> n -> bool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong : n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case : n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : n -> n -> bool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : n -> n -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : n -> n -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module Z = 
 struct 
  type t = z
  
  (** val zero : z **)
  
  let zero =
    Z0
  
  (** val one : z **)
  
  let one =
    Zpos XH
  
  (** val two : z **)
  
  let two =
    Zpos (XO XH)
  
  (** val double : z -> z **)
  
  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)
  
  (** val succ_double : z -> z **)
  
  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)
  
  (** val pred_double : z -> z **)
  
  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)
  
  (** val pos_sub : positive -> positive -> z **)
  
  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)
  
  (** val add : z -> z -> z **)
  
  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))
  
  (** val opp : z -> z **)
  
  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0
  
  (** val succ : z -> z **)
  
  let succ x =
    add x (Zpos XH)
  
  (** val pred : z -> z **)
  
  let pred x =
    add x (Zneg XH)
  
  (** val sub : z -> z -> z **)
  
  let sub m n0 =
    add m (opp n0)
  
  (** val mul : z -> z -> z **)
  
  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))
  
  (** val pow_pos : z -> positive -> z **)
  
  let pow_pos z0 n0 =
    Coq_Pos.iter n0 (mul z0) (Zpos XH)
  
  (** val pow : z -> z -> z **)
  
  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg p -> Z0
  
  (** val square : z -> z **)
  
  let square = function
  | Z0 -> Z0
  | Zpos p -> Zpos (Coq_Pos.square p)
  | Zneg p -> Zpos (Coq_Pos.square p)
  
  (** val compare : z -> z -> comparison **)
  
  let compare x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> Eq
       | Zpos y' -> Lt
       | Zneg y' -> Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' -> Coq_Pos.compare x' y'
       | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)
  
  (** val sgn : z -> z **)
  
  let sgn = function
  | Z0 -> Z0
  | Zpos p -> Zpos XH
  | Zneg p -> Zneg XH
  
  (** val leb : z -> z -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : z -> z -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val geb : z -> z -> bool **)
  
  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true
  
  (** val gtb : z -> z -> bool **)
  
  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false
  
  (** val eqb : z -> z -> bool **)
  
  let rec eqb x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> true
       | _ -> false)
    | Zpos p ->
      (match y with
       | Zpos q -> Coq_Pos.eqb p q
       | _ -> false)
    | Zneg p ->
      (match y with
       | Zneg q -> Coq_Pos.eqb p q
       | _ -> false)
  
  (** val max : z -> z -> z **)
  
  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0
  
  (** val min : z -> z -> z **)
  
  let min n0 m =
    match compare n0 m with
    | Gt -> m
    | _ -> n0
  
  (** val abs : z -> z **)
  
  let abs = function
  | Zneg p -> Zpos p
  | x -> x
  
  (** val abs_nat : z -> int **)
  
  let abs_nat = function
  | Z0 -> 0
  | Zpos p -> Coq_Pos.to_nat p
  | Zneg p -> Coq_Pos.to_nat p
  
  (** val abs_N : z -> n **)
  
  let abs_N = function
  | Z0 -> N0
  | Zpos p -> Npos p
  | Zneg p -> Npos p
  
  (** val to_nat : z -> int **)
  
  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> 0
  
  (** val to_N : z -> n **)
  
  let to_N = function
  | Zpos p -> Npos p
  | _ -> N0
  
  (** val of_nat : int -> z **)
  
  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      Z0)
      (fun n1 -> Zpos
      (Coq_Pos.of_succ_nat n1))
      n0
  
  (** val of_N : n -> z **)
  
  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p
  
  (** val to_pos : z -> positive **)
  
  let to_pos = function
  | Zpos p -> p
  | _ -> XH
  
  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n0 f x =
    match n0 with
    | Zpos p -> Coq_Pos.iter p f x
    | _ -> x
  
  (** val pos_div_eucl : positive -> z -> z*z **)
  
  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let q,r = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b then (mul (Zpos (XO XH)) q),r' else (add (mul (Zpos (XO XH)) q) (Zpos XH)),(sub r' b)
    | XO a' ->
      let q,r = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b then (mul (Zpos (XO XH)) q),r' else (add (mul (Zpos (XO XH)) q) (Zpos XH)),(sub r' b)
    | XH -> if leb (Zpos (XO XH)) b then Z0,(Zpos XH) else (Zpos XH),Z0
  
  (** val div_eucl : z -> z -> z*z **)
  
  let div_eucl a b =
    match a with
    | Z0 -> Z0,Z0
    | Zpos a' ->
      (match b with
       | Z0 -> Z0,Z0
       | Zpos p -> pos_div_eucl a' b
       | Zneg b' ->
         let q,r = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> (opp q),Z0
          | _ -> (opp (add q (Zpos XH))),(add b r)))
    | Zneg a' ->
      (match b with
       | Z0 -> Z0,Z0
       | Zpos p ->
         let q,r = pos_div_eucl a' b in
         (match r with
          | Z0 -> (opp q),Z0
          | _ -> (opp (add q (Zpos XH))),(sub b r))
       | Zneg b' -> let q,r = pos_div_eucl a' (Zpos b') in q,(opp r))
  
  (** val div : z -> z -> z **)
  
  let div a b =
    let q,x = div_eucl a b in q
  
  (** val modulo : z -> z -> z **)
  
  let modulo a b =
    let x,r = div_eucl a b in r
  
  (** val quotrem : z -> z -> z*z **)
  
  let quotrem a b =
    match a with
    | Z0 -> Z0,Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0,a
       | Zpos b0 -> let q,r = N.pos_div_eucl a0 (Npos b0) in (of_N q),(of_N r)
       | Zneg b0 -> let q,r = N.pos_div_eucl a0 (Npos b0) in (opp (of_N q)),(of_N r))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0,a
       | Zpos b0 -> let q,r = N.pos_div_eucl a0 (Npos b0) in (opp (of_N q)),(opp (of_N r))
       | Zneg b0 -> let q,r = N.pos_div_eucl a0 (Npos b0) in (of_N q),(opp (of_N r)))
  
  (** val quot : z -> z -> z **)
  
  let quot a b =
    let x,y = quotrem a b in x
  
  (** val rem : z -> z -> z **)
  
  let rem a b =
    let x,y = quotrem a b in y
  
  (** val even : z -> bool **)
  
  let even = function
  | Z0 -> true
  | Zpos p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  | Zneg p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  
  (** val odd : z -> bool **)
  
  let odd = function
  | Z0 -> false
  | Zpos p ->
    (match p with
     | XO p0 -> false
     | _ -> true)
  | Zneg p ->
    (match p with
     | XO p0 -> false
     | _ -> true)
  
  (** val div2 : z -> z **)
  
  let div2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)
  
  (** val quot2 : z -> z **)
  
  let quot2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p ->
    (match p with
     | XH -> Z0
     | _ -> Zneg (Coq_Pos.div2 p))
  
  (** val log2 : z -> z **)
  
  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0
  
  (** val sqrtrem : z -> z*z **)
  
  let sqrtrem = function
  | Zpos p ->
    let s,m = Coq_Pos.sqrtrem p in
    (match m with
     | Coq_Pos.IsPos r -> (Zpos s),(Zpos r)
     | _ -> (Zpos s),Z0)
  | _ -> Z0,Z0
  
  (** val sqrt : z -> z **)
  
  let sqrt = function
  | Zpos p -> Zpos (Coq_Pos.sqrt p)
  | _ -> Z0
  
  (** val gcd : z -> z -> z **)
  
  let gcd a b =
    match a with
    | Z0 -> abs b
    | Zpos a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
    | Zneg a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
  
  (** val ggcd : z -> z -> z*(z*z) **)
  
  let ggcd a b =
    match a with
    | Z0 -> (abs b),(Z0,(sgn b))
    | Zpos a0 ->
      (match b with
       | Z0 -> (abs a),((sgn a),Z0)
       | Zpos b0 -> let g,p = Coq_Pos.ggcd a0 b0 in let aa,bb = p in (Zpos g),((Zpos aa),(Zpos bb))
       | Zneg b0 -> let g,p = Coq_Pos.ggcd a0 b0 in let aa,bb = p in (Zpos g),((Zpos aa),(Zneg bb)))
    | Zneg a0 ->
      (match b with
       | Z0 -> (abs a),((sgn a),Z0)
       | Zpos b0 -> let g,p = Coq_Pos.ggcd a0 b0 in let aa,bb = p in (Zpos g),((Zneg aa),(Zpos bb))
       | Zneg b0 -> let g,p = Coq_Pos.ggcd a0 b0 in let aa,bb = p in (Zpos g),((Zneg aa),(Zneg bb)))
  
  (** val testbit : z -> z -> bool **)
  
  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> false
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg p -> false
  
  (** val shiftl : z -> z -> z **)
  
  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter p (mul (Zpos (XO XH))) a
  | Zneg p -> Coq_Pos.iter p div2 a
  
  (** val shiftr : z -> z -> z **)
  
  let shiftr a n0 =
    shiftl a (opp n0)
  
  (** val coq_lor : z -> z -> z **)
  
  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
  
  (** val coq_land : z -> z -> z **)
  
  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
  
  (** val ldiff : z -> z -> z **)
  
  let ldiff a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.ldiff a0 b0)
       | Zneg b0 -> of_N (N.coq_land (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))
  
  (** val coq_lxor : z -> z -> z **)
  
  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))
  
  (** val eq_dec : z -> z -> bool **)
  
  let eq_dec x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> true
       | _ -> false)
    | Zpos x0 ->
      (match y with
       | Zpos p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> false)
    | Zneg x0 ->
      (match y with
       | Zneg p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> false)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val leb_spec0 : z -> z -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : z -> z -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_OrderTac = 
   struct 
    module IsTotal = 
     struct 
      
     end
    
    module Tac = 
     struct 
      
     end
   end
  
  (** val sqrt_up : z -> z **)
  
  let sqrt_up a =
    match compare Z0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Z0
  
  (** val log2_up : z -> z **)
  
  let log2_up a =
    match compare (Zpos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> Z0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  module Private_Div = 
   struct 
    module Quot2Div = 
     struct 
      (** val div : z -> z -> z **)
      
      let div =
        quot
      
      (** val modulo : z -> z -> z **)
      
      let modulo =
        rem
     end
    
    module NZQuot = 
     struct 
      
     end
   end
  
  (** val lcm : z -> z -> z **)
  
  let lcm a b =
    abs (mul a (div b (gcd a b)))
  
  (** val eqb_spec : z -> z -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2z : bool -> z **)
  
  let b2z = function
  | true -> Zpos XH
  | false -> Z0
  
  (** val setbit : z -> z -> z **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Zpos XH) n0)
  
  (** val clearbit : z -> z -> z **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Zpos XH) n0)
  
  (** val lnot : z -> z **)
  
  let lnot a =
    pred (opp a)
  
  (** val ones : z -> z **)
  
  let ones n0 =
    pred (shiftl (Zpos XH) n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong : z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case : z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : z -> z -> bool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong : z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case : z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : z -> z -> bool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : z -> z -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : z -> z -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

type 'a indexBound =
  ArrayVector.idx_t
  (* singleton inductive, whose constructor was Build_IndexBound *)

(** val ibound : int -> 'a1 -> 'a1 ArrayVector.storage_t -> 'a1 indexBound -> ArrayVector.idx_t **)

let ibound n0 a bound indexBound0 =
  indexBound0

type 'a boundedIndex = { bindex : 'a; indexb : 'a indexBound }

(** val bindex : int -> 'a1 ArrayVector.storage_t -> 'a1 boundedIndex -> 'a1 **)

let bindex _ _ x = x.bindex

(** val indexb : int -> 'a1 ArrayVector.storage_t -> 'a1 boundedIndex -> 'a1 indexBound **)

let indexb _ _ x = x.indexb

type 'a enumType = ArrayVector.idx_t

(** val boundedIndex_inj_EnumType : int -> 'a1 ArrayVector.storage_t -> 'a1 boundedIndex -> 'a1 enumType **)

let boundedIndex_inj_EnumType len ta idx =
  ibound (Pervasives.succ len) idx.bindex ta idx.indexb

type cache =
| Build_Cache

type cacheFormat = __

type cacheDecode = __

type 't cacheAdd = { addE : (cacheFormat -> 't -> cacheFormat); addD : (cacheDecode -> 't -> cacheDecode) }

(** val addE : cache -> 'a1 cacheAdd -> cacheFormat -> 'a1 -> cacheFormat **)

let addE _ x = x.addE

(** val addD : cache -> 'a1 cacheAdd -> cacheDecode -> 'a1 -> cacheDecode **)

let addD _ x = x.addD

type char = Int64Word.t

(** val test_cache : cache **)

let test_cache =
  Build_Cache

(** val test_cache_add_nat : int cacheAdd **)

let test_cache_add_nat =
  { addE = (fun ce x -> ce); addD = (fun cd x -> cd) }

(** val initialize_Aligned_ByteString : int -> Int64Word.t ArrayVector.storage_t **)

let rec initialize_Aligned_ByteString n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    ArrayVector.empty ())
    (fun n' -> ArrayVector.cons
    ((Int64Word.wzero (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))), n',
    (initialize_Aligned_ByteString n')))
    n0

type w16 = Int64Word.t

(** val add_bytes_into_checksum : Int64Word.t -> Int64Word.t -> w16 -> Int64Word.t **)

let add_bytes_into_checksum = (fun b_hi b_lo checksum ->     let oneC_plus w w' =       let sum = Int64.add w w' in       let mask = Int64.of_int 65535 in       (Int64.add (Int64.logand sum mask)                  (Int64.shift_right_logical sum 16))     in oneC_plus (Int64.logor (Int64.shift_left b_hi 8) b_lo) checksum)

(** val vector_checksum' : int -> Int64Word.t ArrayVector.storage_t -> w16 **)

let vector_checksum' sz bytes =
  ArrayVector.fold_left_pair add_bytes_into_checksum sz bytes
    (Int64Word.wzero (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))
    (Int64Word.wzero (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))

type 'a alignedDecodeM = char ArrayVector.storage_t -> int -> cacheDecode -> (('a*int)*cacheDecode) option

(** val getCurrentByte : cache -> int cacheAdd -> int -> char alignedDecodeM **)

let getCurrentByte cache0 cacheAddNat n0 v idx c =
  match ArrayVector.nth_opt n0 v idx with
  | Some a ->
    Some ((a,(Pervasives.succ
      idx)),(cacheAddNat.addD c (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))
  | None -> None

(** val skipCurrentByte : cache -> int cacheAdd -> int -> unit alignedDecodeM **)

let skipCurrentByte cache0 cacheAddNat n0 v idx c =
  match ArrayVector.nth_opt n0 v idx with
  | Some a ->
    Some (((),(Pervasives.succ
      idx)),(cacheAddNat.addD c (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))
  | None -> None

(** val getCurrentBytes : cache -> int cacheAdd -> int -> int -> Int64Word.t alignedDecodeM **)

let rec getCurrentBytes cache0 cacheAddNat n0 m v idx c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some
    (((Int64Word.w0),idx),c))
    (fun m' ->
    match getCurrentByte cache0 cacheAddNat n0 v idx c with
    | Some a ->
      (match getCurrentBytes cache0 cacheAddNat n0 m' v (let x,y = let x,y = a in x in y) (let x,y = a in y) with
       | Some a0 ->
         Some
           (((Int64Word.append
               (mult m' (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))) (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
               0)))))))) (let x,y = let x,y = a0 in x in x) (let x,y = let x,y = a in x in x)),(let x,y =
                                                                                                  let x,y = a0 in x
                                                                                                in
                                                                                                y)),(let x,y = a0 in
                                                                                                     y))
       | None -> None)
    | None -> None)
    m

type alignedEncodeM =
  char ArrayVector.storage_t -> int -> cacheFormat -> ((char ArrayVector.storage_t*int)*cacheFormat) option

(** val setCurrentByte : cache -> int cacheAdd -> int -> char -> alignedEncodeM **)

let setCurrentByte cache0 cacheAddNat n0 a v idx ce =
  if (<) idx n0
  then Some (((ArrayVector.set_nth n0 v idx a),(Pervasives.succ
         idx)),(cacheAddNat.addE ce (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))
  else None

(** val setByteAt : cache -> int cacheAdd -> int -> Int64Word.t -> int -> alignedEncodeM **)

let setByteAt cache0 cacheAddNat n0 a idx' v idx ce =
  if (<) idx' n0
  then Some (((ArrayVector.set_nth n0 v idx' a),(Pervasives.succ
         idx')),(cacheAddNat.addE ce (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))
  else None

(** val alignedEncode_Nil : cache -> int -> alignedEncodeM **)

let alignedEncode_Nil cache0 numBytes v idx ce =
  if (<) idx (Pervasives.succ numBytes) then Some ((v,idx),ce) else None

(** val setCurrentBytes : cache -> int cacheAdd -> int -> int -> Int64Word.t -> alignedEncodeM **)

let rec setCurrentBytes cache0 cacheAddNat n0 sz w =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    alignedEncode_Nil cache0 n0)
    (fun sz' v idx c ->
    match setCurrentByte cache0 cacheAddNat n0
            (Int64Word.split1' (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
              (mult sz' (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))) w) v idx c with
    | Some a ->
      setCurrentBytes cache0 cacheAddNat n0 sz'
        (Int64Word.split2' (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
          (mult sz' (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))) w) (let x,y = let x,y = a in x in x)
        (let x,y = let x,y = a in x in y) (let x,y = a in y)
    | None -> None)
    sz

(** val calculate_Checksum : cache -> int cacheAdd -> int -> alignedEncodeM **)

let calculate_Checksum cache0 cacheAddNat sz v idx' ce =
  let checksum = vector_checksum' sz v in
  (match setByteAt cache0 cacheAddNat sz
           (Int64Word.split1 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))) (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
             0)))))))) checksum) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
           0)))))))))) v idx' ce with
   | Some a ->
     setByteAt cache0 cacheAddNat sz
       (Int64Word.split2 (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))) (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         0)))))))) checksum) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0))))))))))) (let x,y = let x,y = a in x in x) (let x,y = let x,y = a in x in y) (let x,y = a in y)
   | None -> None)

(** val aligned_decode_enum :
    int -> cache -> int cacheAdd -> Int64Word.t ArrayVector.storage_t -> int -> ArrayVector.idx_t alignedDecodeM **)

let aligned_decode_enum len cache0 cacheAddNat tb n0 v idx c =
  match getCurrentByte cache0 cacheAddNat n0 v idx c with
  | Some a ->
    (match ArrayVector.index (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))) (Pervasives.succ len)
             (let x,y = let x,y = a in x in x) tb with
     | Some a0 -> Some ((a0,(let x,y = let x,y = a in x in y)),(let x,y = a in y))
     | None -> None)
  | None -> None

(** val listAlignedDecodeM : cache -> int -> (int -> 'a1 alignedDecodeM) -> int -> 'a1 list alignedDecodeM **)

let rec listAlignedDecodeM cache0 m a_decode_align n0 x x0 x1 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some
    (([],x0),x1))
    (fun s' ->
    match a_decode_align m x x0 x1 with
    | Some a ->
      (match listAlignedDecodeM cache0 m a_decode_align s' x (let x2,y = let x2,y = a in x2 in y)
               (let x2,y = a in y) with
       | Some a0 ->
         Some
           ((((let x2,y = let x2,y = a in x2 in x2) :: (let x2,y = let x2,y = a0 in x2 in x2)),(let x2,y =
                                                                                                  let x2,y = a0 in
                                                                                                  x2
                                                                                                in
                                                                                                y)),(let x2,y = a0
                                                                                                     in
                                                                                                     y))
       | None -> None)
    | None -> None)
    n0

(** val alignedEncodeList : cache -> ('a1 -> int -> alignedEncodeM) -> 'a1 list -> int -> alignedEncodeM **)

let rec alignedEncodeList cache0 a_format_align as0 sz x x0 x1 =
  match as0 with
  | [] -> if (<) x0 (Pervasives.succ sz) then Some ((x,x0),x1) else None
  | a :: as' ->
    (match a_format_align a sz x x0 x1 with
     | Some a0 ->
       alignedEncodeList cache0 a_format_align as' sz (let x2,y = let x2,y = a0 in x2 in x2)
         (let x2,y = let x2,y = a0 in x2 in y) (let x2,y = a0 in y)
     | None -> None)

type iPv4_Packet = { totalLength : Int64Word.t; iD : Int64Word.t; dF : bool; mF : bool;
                     fragmentOffset : Int64Word.t; tTL : Int64Word.t; protocol : char list enumType;
                     sourceAddress : Int64Word.t; destAddress : Int64Word.t; options : Int64Word.t list }

(** val totalLength : iPv4_Packet -> Int64Word.t **)

let totalLength x = x.totalLength

(** val iD : iPv4_Packet -> Int64Word.t **)

let iD x = x.iD

(** val dF : iPv4_Packet -> bool **)

let dF x = x.dF

(** val mF : iPv4_Packet -> bool **)

let mF x = x.mF

(** val fragmentOffset : iPv4_Packet -> Int64Word.t **)

let fragmentOffset x = x.fragmentOffset

(** val tTL : iPv4_Packet -> Int64Word.t **)

let tTL x = x.tTL

(** val protocol : iPv4_Packet -> char list enumType **)

let protocol x = x.protocol

(** val sourceAddress : iPv4_Packet -> Int64Word.t **)

let sourceAddress x = x.sourceAddress

(** val destAddress : iPv4_Packet -> Int64Word.t **)

let destAddress x = x.destAddress

(** val options : iPv4_Packet -> Int64Word.t list **)

let options x = x.options

(** val protocolTypeCodes : Int64Word.t ArrayVector.storage_t **)

let protocolTypeCodes =
  Obj.magic (ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ 0)), (ArrayVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ 0), (ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), 0, ArrayVector.empty ()))))))

(** val iPv4_Packet_Header_Len : iPv4_Packet -> int **)

let iPv4_Packet_Header_Len ip4 =
  plus (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))
    (length ip4.options)

(** val iPv4_encoder_impl :
    iPv4_Packet -> int -> char ArrayVector.storage_t -> ((char ArrayVector.storage_t*int)*cacheFormat) option **)

let iPv4_encoder_impl r sz v =
  match match setCurrentByte test_cache test_cache_add_nat sz
                (Int64Word.combine (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
                  (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
                    (iPv4_Packet_Header_Len r)) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  0))))
                  (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))) v 0 (Obj.magic ()) with
        | Some a ->
          (match setCurrentByte test_cache test_cache_add_nat sz
                   (Int64Word.wzero (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))
                   (let x,y = let x,y = a in x in x) (let x,y = let x,y = a in x in y) (let x,y = a in y) with
           | Some a0 ->
             (match setCurrentBytes test_cache test_cache_add_nat sz (Pervasives.succ (Pervasives.succ 0))
                      r.totalLength (let x,y = let x,y = a0 in x in x) (let x,y = let x,y = a0 in x in y)
                      (let x,y = a0 in y) with
              | Some a1 ->
                (match setCurrentBytes test_cache test_cache_add_nat sz (Pervasives.succ (Pervasives.succ 0)) r.iD
                         (let x,y = let x,y = a1 in x in x) (let x,y = let x,y = a1 in x in y) (let x,y = a1 in y) with
                 | Some a2 ->
                   (match setCurrentBytes test_cache test_cache_add_nat sz (Pervasives.succ (Pervasives.succ 0))
                            (Int64Word.combine (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))
                              r.fragmentOffset
                              (plus (Pervasives.succ 0) (plus (Pervasives.succ 0) (Pervasives.succ 0)))
                              (Int64Word.combine (Pervasives.succ 0) (Int64Word.ws (r.mF, 0, (Int64Word.w0)))
                                (plus (Pervasives.succ 0) (Pervasives.succ 0))
                                (Int64Word.combine (Pervasives.succ 0) (Int64Word.ws (r.dF, 0, (Int64Word.w0)))
                                  (Pervasives.succ 0) (Int64Word.wzero (Pervasives.succ 0)))))
                            (let x,y = let x,y = a2 in x in x) (let x,y = let x,y = a2 in x in y)
                            (let x,y = a2 in y) with
                    | Some a3 ->
                      (match setCurrentByte test_cache test_cache_add_nat sz r.tTL
                               (let x,y = let x,y = a3 in x in x) (let x,y = let x,y = a3 in x in y)
                               (let x,y = a3 in y) with
                       | Some a4 ->
                         (match setCurrentByte test_cache test_cache_add_nat sz
                                  (ArrayVector.nth (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
                                    protocolTypeCodes r.protocol) (let x,y = let x,y = a4 in x in x)
                                  (let x,y = let x,y = a4 in x in y) (let x,y = a4 in y) with
                          | Some a5 ->
                            alignedEncode_Nil test_cache sz (let x,y = let x,y = a5 in x in x)
                              (let x,y = let x,y = a5 in x in y) (let x,y = a5 in y)
                          | None -> None)
                       | None -> None)
                    | None -> None)
                 | None -> None)
              | None -> None)
           | None -> None)
        | None -> None with
  | Some a ->
    (match setCurrentByte test_cache test_cache_add_nat sz
             (Int64Word.wzero (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))) (let x,y = let x,y = a in x in x)
             (let x,y = let x,y = a in x in y) (let x,y = a in y) with
     | Some a0 ->
       (match setCurrentByte test_cache test_cache_add_nat sz
                (Int64Word.wzero (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))
                (let x,y = let x,y = a0 in x in x) (let x,y = let x,y = a0 in x in y) (let x,y = a0 in y) with
        | Some a1 ->
          (match match setCurrentBytes test_cache test_cache_add_nat sz (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ 0)))) r.sourceAddress (let x,y = let x,y = a1 in x in x)
                         (let x,y = let x,y = a1 in x in y) (let x,y = a1 in y) with
                 | Some a2 ->
                   (match setCurrentBytes test_cache test_cache_add_nat sz (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ 0)))) r.destAddress (let x,y = let x,y = a2 in x in x)
                            (let x,y = let x,y = a2 in x in y) (let x,y = a2 in y) with
                    | Some a3 ->
                      (match alignedEncodeList test_cache (fun a4 sz0 ->
                               setCurrentBytes test_cache test_cache_add_nat sz0 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ 0)))) a4) r.options sz
                               (let x,y = let x,y = a3 in x in x) (let x,y = let x,y = a3 in x in y)
                               (let x,y = a3 in y) with
                       | Some a4 ->
                         alignedEncode_Nil test_cache sz (let x,y = let x,y = a4 in x in x)
                           (let x,y = let x,y = a4 in x in y) (let x,y = a4 in y)
                       | None -> None)
                    | None -> None)
                 | None -> None with
           | Some a2 ->
             calculate_Checksum test_cache test_cache_add_nat sz (let x,y = let x,y = a2 in x in x)
               (let x,y = let x,y = a2 in x in y) (let x,y = a2 in y)
           | None -> None)
        | None -> None)
     | None -> None)
  | None -> None

(** val iPv4_decoder_impl : int -> char ArrayVector.storage_t -> ((iPv4_Packet*int)*cacheDecode) option **)

let iPv4_decoder_impl sz v =
  match getCurrentByte test_cache test_cache_add_nat sz v 0 (Obj.magic ()) with
  | Some a ->
    let b = let x,y = let x,y = a in x in x in
    let idx = let x,y = let x,y = a in x in y in
    let c = let x,y = a in y in
    if Int64Word.weq (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
         (id
           (Int64Word.split1' (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
             (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))) b))
         (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
           (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))
    then (match skipCurrentByte test_cache test_cache_add_nat sz v idx c with
          | Some a0 ->
            (match getCurrentByte test_cache test_cache_add_nat sz v (let x,y = let x,y = a0 in x in y)
                     (let x,y = a0 in y) with
             | Some a1 ->
               (match getCurrentByte test_cache test_cache_add_nat sz v (let x,y = let x,y = a1 in x in y)
                        (let x,y = a1 in y) with
                | Some a2 ->
                  let a3 =
                    ((Int64Word.append (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
                       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
                       (let x,y = let x,y = a2 in x in x) (let x,y = let x,y = a1 in x in x)),(let x,y =
                                                                                                 let x,y = a2 in x
                                                                                               in
                                                                                               y)),(let x,y = a2 in
                                                                                                    y)
                  in
                  let w = let x,y = let x,y = a3 in x in x in
                  (match getCurrentByte test_cache test_cache_add_nat sz v (let x,y = let x,y = a3 in x in y)
                           (let x,y = a3 in y) with
                   | Some a4 ->
                     (match getCurrentByte test_cache test_cache_add_nat sz v (let x,y = let x,y = a4 in x in y)
                              (let x,y = a4 in y) with
                      | Some a5 ->
                        let a6 =
                          ((Int64Word.append (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
                             (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
                             (let x,y = let x,y = a5 in x in x) (let x,y = let x,y = a4 in x in x)),(let x,y =
                                                                                                       let x,y = a5
                                                                                                       in
                                                                                                       x
                                                                                                     in
                                                                                                     y)),(let x,y =
                                                                                                           a5
                                                                                                          in
                                                                                                          y)
                        in
                        (match getCurrentByte test_cache test_cache_add_nat sz v (let x,y = let x,y = a6 in x in y)
                                 (let x,y = a6 in y) with
                         | Some a7 ->
                           (match getCurrentByte test_cache test_cache_add_nat sz v
                                    (let x,y = let x,y = a7 in x in y) (let x,y = a7 in y) with
                            | Some a8 ->
                              let a9 =
                                ((Int64Word.append (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0)))))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0)))))))) (let x,y = let x,y = a8 in x in x)
                                   (let x,y = let x,y = a7 in x in x)),(let x,y = let x,y = a8 in x in y)),(
                                                                                                           let x,y =
                                                                                                           a8
                                                                                                           in
                                                                                                           y)
                              in
                              let w0 = let x,y = let x,y = a9 in x in x in
                              (match getCurrentByte test_cache test_cache_add_nat sz v
                                       (let x,y = let x,y = a9 in x in y) (let x,y = a9 in y) with
                               | Some a10 ->
                                 (match aligned_decode_enum (Pervasives.succ (Pervasives.succ 0)) test_cache
                                          test_cache_add_nat protocolTypeCodes sz v
                                          (let x,y = let x,y = a10 in x in y) (let x,y = a10 in y) with
                                  | Some a11 ->
                                    (match skipCurrentByte test_cache test_cache_add_nat sz v
                                             (let x,y = let x,y = a11 in x in y) (let x,y = a11 in y) with
                                     | Some a12 ->
                                       (match getCurrentByte test_cache test_cache_add_nat sz v
                                                (let x,y = let x,y = a12 in x in y) (let x,y = a12 in y) with
                                        | Some a13 ->
                                          (match getCurrentByte test_cache test_cache_add_nat sz v
                                                   (let x,y = let x,y = a13 in x in y) (let x,y = a13 in y) with
                                           | Some a14 ->
                                             (match getCurrentByte test_cache test_cache_add_nat sz v
                                                      (let x,y = let x,y = a14 in x in y) (let x,y = a14 in y) with
                                              | Some a15 ->
                                                (match getCurrentByte test_cache test_cache_add_nat sz v
                                                         (let x,y = let x,y = a15 in x in y) (let x,y = a15 in y) with
                                                 | Some a16 ->
                                                   let a17 =
                                                     ((Int64Word.append (Pervasives.succ (Pervasives.succ
                                                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                        (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
                                                        (plus (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                          (Pervasives.succ (Pervasives.succ 0))))))))
                                                          (plus (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ 0))))))))
                                                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ 0))))))))))
                                                        (let x,y = let x,y = a16 in x in x)
                                                        (Int64Word.append (Pervasives.succ (Pervasives.succ
                                                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                          (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                          0))))))))
                                                          (plus (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ 0))))))))
                                                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ 0)))))))))
                                                          (let x,y = let x,y = a15 in x in x)
                                                          (Int64Word.append (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            0)))))))) (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            (Pervasives.succ (Pervasives.succ (Pervasives.succ
                                                            0)))))))) (let x,y = let x,y = a14 in x in x)
                                                            (let x,y = let x,y = a13 in x in x)))),(let x,y =
                                                                                                      let x,y = a16
                                                                                                      in
                                                                                                      x
                                                                                                    in
                                                                                                    y)),(let x,y =
                                                                                                           a16
                                                                                                         in
                                                                                                         y)
                                                   in
                                                   (match getCurrentByte test_cache test_cache_add_nat sz v
                                                            (let x,y = let x,y = a17 in x in y) (let x,y = a17 in y) with
                                                    | Some a18 ->
                                                      (match getCurrentByte test_cache test_cache_add_nat sz v
                                                               (let x,y = let x,y = a18 in x in y)
                                                               (let x,y = a18 in y) with
                                                       | Some a19 ->
                                                         (match getCurrentByte test_cache test_cache_add_nat sz v
                                                                  (let x,y = let x,y = a19 in x in y)
                                                                  (let x,y = a19 in y) with
                                                          | Some a20 ->
                                                            (match getCurrentByte test_cache test_cache_add_nat sz v
                                                                     (let x,y = let x,y = a20 in x in y)
                                                                     (let x,y = a20 in y) with
                                                             | Some a21 ->
                                                               let a22 =
                                                                 ((Int64Word.append (Pervasives.succ
                                                                    (Pervasives.succ (Pervasives.succ
                                                                    (Pervasives.succ (Pervasives.succ
                                                                    (Pervasives.succ (Pervasives.succ
                                                                    (Pervasives.succ 0))))))))
                                                                    (plus (Pervasives.succ (Pervasives.succ
                                                                      (Pervasives.succ (Pervasives.succ
                                                                      (Pervasives.succ (Pervasives.succ
                                                                      (Pervasives.succ (Pervasives.succ 0))))))))
                                                                      (plus (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ 0))))))))
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ 0))))))))))
                                                                    (let x,y = let x,y = a21 in x in x)
                                                                    (Int64Word.append (Pervasives.succ
                                                                      (Pervasives.succ (Pervasives.succ
                                                                      (Pervasives.succ (Pervasives.succ
                                                                      (Pervasives.succ (Pervasives.succ
                                                                      (Pervasives.succ 0))))))))
                                                                      (plus (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ 0))))))))
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ 0)))))))))
                                                                      (let x,y = let x,y = a20 in x in x)
                                                                      (Int64Word.append (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ 0)))))))) (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ (Pervasives.succ
                                                                        (Pervasives.succ 0))))))))
                                                                        (let x,y = let x,y = a19 in x in x)
                                                                        (let x,y = let x,y = a18 in x in x)))),
                                                                 (let x,y = let x,y = a21 in x in y)),(let x,y = a21
                                                                                                       in
                                                                                                       y)
                                                               in
                                                               (match listAlignedDecodeM test_cache sz
                                                                        (fun numBytes ->
                                                                        getCurrentBytes test_cache
                                                                          test_cache_add_nat numBytes
                                                                          (Pervasives.succ (Pervasives.succ
                                                                          (Pervasives.succ (Pervasives.succ 0)))))
                                                                        (minus
                                                                          (Int64Word.wordToNat (Pervasives.succ
                                                                            (Pervasives.succ (Pervasives.succ
                                                                            (Pervasives.succ 0))))
                                                                            (id
                                                                              (Int64Word.split2' (Pervasives.succ
                                                                                (Pervasives.succ (Pervasives.succ
                                                                                (Pervasives.succ 0))))
                                                                                (Pervasives.succ (Pervasives.succ
                                                                                (Pervasives.succ (Pervasives.succ
                                                                                0)))) b))) (Pervasives.succ
                                                                          (Pervasives.succ (Pervasives.succ
                                                                          (Pervasives.succ (Pervasives.succ 0))))))
                                                                        v (let x,y = let x,y = a22 in x in y)
                                                                        (let x,y = a22 in y) with
                                                                | Some a23 ->
                                                                  let l = let x,y = let x,y = a23 in x in x in
                                                                  let idx0 = let x,y = let x,y = a23 in x in y in
                                                                  let c0 = let x,y = a23 in y in
                                                                  if (&&)
                                                                       ((&&)
                                                                         (if lt_dec (length l) (Pervasives.succ
                                                                               (Pervasives.succ (Pervasives.succ
                                                                               (Pervasives.succ (Pervasives.succ
                                                                               (Pervasives.succ (Pervasives.succ
                                                                               (Pervasives.succ (Pervasives.succ
                                                                               (Pervasives.succ (Pervasives.succ
                                                                               0)))))))))))
                                                                          then true
                                                                          else false)
                                                                         (if lt_dec
                                                                               (plus (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ
                                                                                 0))))))))))))))))))))
                                                                                 (mult (Pervasives.succ
                                                                                   (Pervasives.succ (Pervasives.succ
                                                                                   (Pervasives.succ 0))))
                                                                                   (length l)))
                                                                               (Int64Word.wordToNat (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ 0))))))))))))))))
                                                                                 w)
                                                                          then true
                                                                          else false))
                                                                       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                          (fun _ ->
                                                                          false)
                                                                          (fun m1 ->
                                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                            (fun _ ->
                                                                            false)
                                                                            (fun m2 ->
                                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                              (fun _ ->
                                                                              false)
                                                                              (fun m3 ->
                                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                                (fun _ ->
                                                                                false)
                                                                                (fun m4 ->
                                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                                  (fun _ ->
                                                                                  false)
                                                                                  (fun m5 ->
                                                                                  (=) (length l) m5)
                                                                                  m4)
                                                                                m3)
                                                                              m2)
                                                                            m1)
                                                                          (Int64Word.wordToNat (Pervasives.succ
                                                                            (Pervasives.succ (Pervasives.succ
                                                                            (Pervasives.succ 0))))
                                                                            (id
                                                                              (Int64Word.split2' (Pervasives.succ
                                                                                (Pervasives.succ (Pervasives.succ
                                                                                (Pervasives.succ 0))))
                                                                                (Pervasives.succ (Pervasives.succ
                                                                                (Pervasives.succ (Pervasives.succ
                                                                                0)))) b))))
                                                                  then Some (({ totalLength = w; iD =
                                                                         (let x,y = let x,y = a6 in x in x); dF =
                                                                         (Int64Word.whd (Pervasives.succ 0)
                                                                           (Int64Word.wtl (Pervasives.succ
                                                                             (Pervasives.succ 0))
                                                                             (Int64Word.wtl (Pervasives.succ
                                                                               (Pervasives.succ (Pervasives.succ
                                                                               0)))
                                                                               (Int64Word.wtl (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ 0))))
                                                                                 (Int64Word.wtl (Pervasives.succ
                                                                                   (Pervasives.succ (Pervasives.succ
                                                                                   (Pervasives.succ (Pervasives.succ
                                                                                   0)))))
                                                                                   (Int64Word.wtl (Pervasives.succ
                                                                                     (Pervasives.succ
                                                                                     (Pervasives.succ
                                                                                     (Pervasives.succ
                                                                                     (Pervasives.succ
                                                                                     (Pervasives.succ 0))))))
                                                                                     (Int64Word.wtl (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ 0)))))))
                                                                                       (Int64Word.wtl
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ 0))))))))
                                                                                         (Int64Word.wtl
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           0)))))))))
                                                                                           (Int64Word.wtl
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             0))))))))))
                                                                                             (Int64Word.wtl
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               0)))))))))))
                                                                                               (Int64Word.wtl
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 0))))))))))))
                                                                                                 (Int64Word.wtl
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   0)))))))))))))
                                                                                                   (Int64Word.wtl
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     0))))))))))))))
                                                                                                     (Int64Word.wtl
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       (Pervasives.succ
                                                                                                       0)))))))))))))))
                                                                                                       w0)))))))))))))));
                                                                         mF =
                                                                         (Int64Word.whd (Pervasives.succ
                                                                           (Pervasives.succ 0))
                                                                           (Int64Word.wtl (Pervasives.succ
                                                                             (Pervasives.succ (Pervasives.succ 0)))
                                                                             (Int64Word.wtl (Pervasives.succ
                                                                               (Pervasives.succ (Pervasives.succ
                                                                               (Pervasives.succ 0))))
                                                                               (Int64Word.wtl (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 (Pervasives.succ (Pervasives.succ
                                                                                 0)))))
                                                                                 (Int64Word.wtl (Pervasives.succ
                                                                                   (Pervasives.succ (Pervasives.succ
                                                                                   (Pervasives.succ (Pervasives.succ
                                                                                   (Pervasives.succ 0))))))
                                                                                   (Int64Word.wtl (Pervasives.succ
                                                                                     (Pervasives.succ
                                                                                     (Pervasives.succ
                                                                                     (Pervasives.succ
                                                                                     (Pervasives.succ
                                                                                     (Pervasives.succ
                                                                                     (Pervasives.succ 0)))))))
                                                                                     (Int64Word.wtl (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ
                                                                                       (Pervasives.succ 0))))))))
                                                                                       (Int64Word.wtl
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ
                                                                                         (Pervasives.succ 0)))))))))
                                                                                         (Int64Word.wtl
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           (Pervasives.succ
                                                                                           0))))))))))
                                                                                           (Int64Word.wtl
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             (Pervasives.succ
                                                                                             0)))))))))))
                                                                                             (Int64Word.wtl
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               (Pervasives.succ
                                                                                               0))))))))))))
                                                                                               (Int64Word.wtl
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 (Pervasives.succ
                                                                                                 0)))))))))))))
                                                                                                 (Int64Word.wtl
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   (Pervasives.succ
                                                                                                   0))))))))))))))
                                                                                                   (Int64Word.wtl
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     (Pervasives.succ
                                                                                                     0)))))))))))))))
                                                                                                     w0))))))))))))));
                                                                         fragmentOffset =
                                                                         (id
                                                                           (Int64Word.split2'
                                                                             (plus
                                                                               (plus (Pervasives.succ 0)
                                                                                 (Pervasives.succ 0))
                                                                               (Pervasives.succ 0)) (Pervasives.succ
                                                                             (Pervasives.succ (Pervasives.succ
                                                                             (Pervasives.succ (Pervasives.succ
                                                                             (Pervasives.succ (Pervasives.succ
                                                                             (Pervasives.succ (Pervasives.succ
                                                                             (Pervasives.succ (Pervasives.succ
                                                                             (Pervasives.succ (Pervasives.succ
                                                                             0))))))))))))) w0)); tTL =
                                                                         (let x,y = let x,y = a10 in x in x);
                                                                         protocol =
                                                                         (let x,y = let x,y = a11 in x in x);
                                                                         sourceAddress =
                                                                         (let x,y = let x,y = a17 in x in x);
                                                                         destAddress =
                                                                         (let x,y = let x,y = a22 in x in x);
                                                                         options = l },idx0),c0)
                                                                  else None
                                                                | None -> None)
                                                             | None -> None)
                                                          | None -> None)
                                                       | None -> None)
                                                    | None -> None)
                                                 | None -> None)
                                              | None -> None)
                                           | None -> None)
                                        | None -> None)
                                     | None -> None)
                                  | None -> None)
                               | None -> None)
                            | None -> None)
                         | None -> None)
                      | None -> None)
                   | None -> None)
                | None -> None)
             | None -> None)
          | None -> None)
    else None
  | None -> None

(** val bin_pkt : Int64Word.t ArrayVector.storage_t **)

let bin_pkt =
  ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))), (ArrayVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))), (ArrayVector.cons ((Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))), (ArrayVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))), (ArrayVector.cons
    ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))),
    (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))),
    (ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))), (ArrayVector.cons
    ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))), (ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))), (ArrayVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))),
    (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (true, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (true, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))),
    (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))), (ArrayVector.cons ((Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (ArrayVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)),
    (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (ArrayVector.cons
    ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (ArrayVector.cons ((Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (ArrayVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ 0)), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))), (Pervasives.succ 0),
    (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), 0, ArrayVector.empty ())))))))))))))))))))))))))))))))))))))))))))))))

(** val pkt : iPv4_Packet **)

let pkt =
  { totalLength = (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))); iD =
    (Int64Word.wones (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))); dF =
    false; mF = false; fragmentOffset =
    (Int64Word.wzero (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))))))))); tTL = (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))); protocol = (ArrayVector.zero
    (Pervasives.succ (Pervasives.succ 0))); sourceAddress = (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (true, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))); destAddress = (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))); options = [] }

(** val injectEnum : int -> 'a1 ArrayVector.storage_t -> ArrayVector.idx_t -> 'a1 **)

let injectEnum n0 gallina_constructors enum_member =
  ArrayVector.nth n0 gallina_constructors enum_member

(** val makeDecoder :
    int -> (int -> char ArrayVector.storage_t -> (('a1*int)*'a2) option) -> char ArrayVector.storage_t -> 'a1 option **)

let makeDecoder sz impl bs =
  match impl sz bs with
  | Some p -> let p0,a = p in let pkt0,n0 = p0 in Some pkt0
  | None -> None

(** val makeEncoder :
    int -> ('a1 -> int -> char ArrayVector.storage_t -> ((char ArrayVector.storage_t*int)*'a2) option) -> 'a1 ->
    char ArrayVector.storage_t -> char ArrayVector.storage_t option **)

let makeEncoder sz impl pkt0 out =
  match impl pkt0 sz out with
  | Some p -> let p0,a = p in let out0,n0 = p0 in Some out0
  | None -> None

(** val fiat_ipv4_decode : int -> char ArrayVector.storage_t -> iPv4_Packet option **)

let fiat_ipv4_decode sz =
  makeDecoder sz iPv4_decoder_impl

type fiat_ipv4_protocol =
| ICMP
| TCP
| UDP

(** val fiat_ipv4_protocol_to_enum : fiat_ipv4_protocol -> char list enumType **)

let fiat_ipv4_protocol_to_enum = function
| ICMP ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ 0))
    (Obj.magic (ArrayVector.cons (('I'::('C'::('M'::('P'::[])))), (Pervasives.succ (Pervasives.succ 0)),
      (ArrayVector.cons (('T'::('C'::('P'::[]))), (Pervasives.succ 0), (ArrayVector.cons (('U'::('D'::('P'::[]))),
      0, ArrayVector.empty ()))))))) { bindex = ('I'::('C'::('M'::('P'::[])))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) 0 (ArrayVector.zero
      (Pervasives.succ (Pervasives.succ 0)))) }
| TCP ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ 0))
    (Obj.magic (ArrayVector.cons (('I'::('C'::('M'::('P'::[])))), (Pervasives.succ (Pervasives.succ 0)),
      (ArrayVector.cons (('T'::('C'::('P'::[]))), (Pervasives.succ 0), (ArrayVector.cons (('U'::('D'::('P'::[]))),
      0, ArrayVector.empty ()))))))) { bindex = ('T'::('C'::('P'::[]))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ 0) (ArrayVector.zero
      (Pervasives.succ 0))) }
| UDP ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ 0))
    (Obj.magic (ArrayVector.cons (('I'::('C'::('M'::('P'::[])))), (Pervasives.succ (Pervasives.succ 0)),
      (ArrayVector.cons (('T'::('C'::('P'::[]))), (Pervasives.succ 0), (ArrayVector.cons (('U'::('D'::('P'::[]))),
      0, ArrayVector.empty ()))))))) { bindex = ('U'::('D'::('P'::[]))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ 0) (Pervasives.succ (Pervasives.succ 0)) (ArrayVector.zero 0)) }

(** val fiat_ipv4_enum_to_protocol : char list enumType -> fiat_ipv4_protocol **)

let fiat_ipv4_enum_to_protocol proto =
  injectEnum (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) (ArrayVector.cons (ICMP, (Pervasives.succ
    (Pervasives.succ 0)), (ArrayVector.cons (TCP, (Pervasives.succ 0), (ArrayVector.cons (UDP, 0,
    ArrayVector.empty ())))))) proto

(** val fiat_ipv4_encode : int -> iPv4_Packet -> char ArrayVector.storage_t -> char ArrayVector.storage_t option **)

let fiat_ipv4_encode sz =
  makeEncoder sz iPv4_encoder_impl

(** val word_split_hd_test : bool **)

let word_split_hd_test =
  Int64Word.word_split_hd (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
    (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))))))))))))))))))))))

(** val word_split_tl_test : int **)

let word_split_tl_test =
  Int64Word.wordToNat (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
    (Int64Word.word_split_tl (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
      (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))))))))))))))))))))))))))))))

(** val alignword_split1'_test : int **)

let alignword_split1'_test =
  Int64Word.wordToNat (Pervasives.succ (Pervasives.succ 0))
    (Int64Word.split1' (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
      (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))))))))))))))))))))))))))))))

(** val alignword_split2'_test : int **)

let alignword_split2'_test =
  Int64Word.wordToNat (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
    (Int64Word.split2' (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
      (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))))))))))))))))))))))))))))))

(** val split1_test : int **)

let split1_test =
  Int64Word.wordToNat (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
    (Int64Word.split1 (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) (Pervasives.succ (Pervasives.succ 0))
      (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))))))))))))))))))))))))))))))

(** val split2_test : int **)

let split2_test =
  Int64Word.wordToNat (Pervasives.succ (Pervasives.succ 0))
    (Int64Word.split2 (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) (Pervasives.succ (Pervasives.succ 0))
      (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))))))))))))))))))))))))))))))

(** val combine_test : int **)

let combine_test =
  Int64Word.wordToNat
    (plus (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))
    (Int64Word.combine (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))
      (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        0))))))))))))))))))))))))))))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))
      (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ 0))))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))

(** val append_word_test : int **)

let append_word_test =
  Int64Word.wordToNat
    (plus (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))
    (Int64Word.append (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))) (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))
      (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))) (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))
      (Int64Word.natToWord (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))))) (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val fiat_ipv4_decode_bench : unit -> iPv4_Packet option **)

let fiat_ipv4_decode_bench x =
  fiat_ipv4_decode (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))) bin_pkt

(** val fiat_ipv4_decode_test : iPv4_Packet option **)

let fiat_ipv4_decode_test =
  fiat_ipv4_decode_bench ()

(** val fiat_ipv4_decode_reference : iPv4_Packet option **)

let fiat_ipv4_decode_reference =
  Some { totalLength = (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))); iD = (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))); dF = false; mF = false; fragmentOffset = (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))); tTL = (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))); protocol = (ArrayVector.zero (Pervasives.succ
    (Pervasives.succ 0))); sourceAddress = (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))))))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (true, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))); destAddress = (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))); options = [] }

(** val fiat_ipv4_encode_bench : unit -> char ArrayVector.storage_t option **)

let fiat_ipv4_encode_bench x =
  fiat_ipv4_encode (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))) pkt
    (initialize_Aligned_ByteString (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))))

(** val fiat_ipv4_encode_test : char ArrayVector.storage_t option **)

let fiat_ipv4_encode_test =
  fiat_ipv4_encode_bench ()

(** val fiat_ipv4_encode_reference : Int64Word.t ArrayVector.storage_t option **)

let fiat_ipv4_encode_reference =
  Some (ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))))), (ArrayVector.cons ((Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))))))), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))))), (ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (true, (Pervasives.succ 0),
    (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))), (ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (true, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))), (ArrayVector.cons
    ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))), (ArrayVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))),
    (ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))), (ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))),
    (ArrayVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (true, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))), (ArrayVector.cons ((Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)),
    (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (true, (Pervasives.succ 0),
    (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (ArrayVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (ArrayVector.cons
    ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (ArrayVector.cons ((Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (ArrayVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))),
    (Pervasives.succ (Pervasives.succ 0)), (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))), (Pervasives.succ 0),
    (ArrayVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (true, (Pervasives.succ 0), (Int64Word.ws (true, 0,
    (Int64Word.w0))))))))))))))))), 0, ArrayVector.empty ()))))))))))))))))))))))))))))))))))))))))

