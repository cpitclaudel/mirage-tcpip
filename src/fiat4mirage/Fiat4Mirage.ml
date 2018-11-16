
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> OCamlNativeInt.t **)

let rec length = function
| [] -> 0
| _ :: l' -> Pervasives.succ (length l')

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

let compSpec2Type _ _ =
  compareSpec2Type

(** val id : 'a1 -> 'a1 **)

let id x =
  x

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type int =
| Pos of uint
| Neg of uint

(** val nzhead : uint -> uint **)

let rec nzhead d = match d with
| D0 d0 -> nzhead d0
| _ -> d

(** val unorm : uint -> uint **)

let unorm d =
  match nzhead d with
  | Nil -> D0 Nil
  | x -> x

(** val norm : int -> int **)

let norm = function
| Pos d0 -> Pos (unorm d0)
| Neg d0 -> (match nzhead d0 with
             | Nil -> Pos (D0 Nil)
             | x -> Neg x)

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil

module Little =
 struct
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> D0 (succ d0)
 end

(** val add : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

let rec add = (+)

(** val mul : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

let rec mul = ( * )

(** val sub : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

let rec sub = fun (x: OCamlNativeInt.t) (y: OCamlNativeInt.t) ->
if x <= y then 0 else (x - y)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module Nat =
 struct
  type t = OCamlNativeInt.t

  (** val zero : OCamlNativeInt.t **)

  let zero =
    0

  (** val one : OCamlNativeInt.t **)

  let one =
    Pervasives.succ 0

  (** val two : OCamlNativeInt.t **)

  let two =
    Pervasives.succ (Pervasives.succ 0)

  (** val succ : OCamlNativeInt.t -> OCamlNativeInt.t **)

  let succ x =
    Pervasives.succ x

  (** val pred : OCamlNativeInt.t -> OCamlNativeInt.t **)

  let pred n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun u -> u)
      n0

  (** val add : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec add n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Pervasives.succ (add p m))
      n0

  (** val double : OCamlNativeInt.t -> OCamlNativeInt.t **)

  let double n0 =
    add n0 n0

  (** val mul : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec mul n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n0

  (** val sub : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec sub n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val ltb : OCamlNativeInt.t -> OCamlNativeInt.t -> bool **)

  let ltb n0 m =
    (<=) (Pervasives.succ n0) m

  (** val compare : OCamlNativeInt.t -> OCamlNativeInt.t -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt

  (** val max : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec max n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun m' -> Pervasives.succ (max n' m'))
        m)
      n0

  (** val min : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec min n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 0)
        (fun m' -> Pervasives.succ (min n' m'))
        m)
      n0

  (** val even : OCamlNativeInt.t -> bool **)

  let rec even n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n1)
      n0

  (** val odd : OCamlNativeInt.t -> bool **)

  let odd n0 =
    negb (even n0)

  (** val pow : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec pow n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ 0)
      (fun m0 -> mul n0 (pow n0 m0))
      m

  (** val tail_add :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec tail_add n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n1 -> tail_add n1 (Pervasives.succ m))
      n0

  (** val tail_addmul :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t ->
      OCamlNativeInt.t **)

  let rec tail_addmul r n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> r)
      (fun n1 -> tail_addmul (tail_add m r) n1 m)
      n0

  (** val tail_mul :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let tail_mul n0 m =
    tail_addmul 0 n0 m

  (** val of_uint_acc : uint -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec of_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 d0 ->
      of_uint_acc d0
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) acc)
    | D1 d0 ->
      of_uint_acc d0 (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) acc))
    | D2 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) acc)))
    | D3 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) acc))))
    | D4 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) acc)))))
    | D5 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) acc))))))
    | D6 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) acc)))))))
    | D7 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) acc))))))))
    | D8 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) acc)))))))))
    | D9 d0 ->
      of_uint_acc d0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ
        (tail_mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))) acc))))))))))

  (** val of_uint : uint -> OCamlNativeInt.t **)

  let of_uint d =
    of_uint_acc d 0

  (** val to_little_uint : OCamlNativeInt.t -> uint -> uint **)

  let rec to_little_uint n0 acc =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> acc)
      (fun n1 -> to_little_uint n1 (Little.succ acc))
      n0

  (** val to_uint : OCamlNativeInt.t -> uint **)

  let to_uint n0 =
    rev (to_little_uint n0 (D0 Nil))

  (** val of_int : int -> OCamlNativeInt.t option **)

  let of_int d =
    match norm d with
    | Pos u -> Some (of_uint u)
    | Neg _ -> None

  (** val to_int : OCamlNativeInt.t -> int **)

  let to_int n0 =
    Pos (to_uint n0)

  (** val divmod :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t ->
      OCamlNativeInt.t -> OCamlNativeInt.t*OCamlNativeInt.t **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> q,u)
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Pervasives.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let div x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> let x0,_ = divmod x y' 0 y' in x0)
      y

  (** val modulo :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> sub y' (let _,y0 = divmod x y' 0 y' in y0))
      y

  (** val gcd : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec gcd a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> b)
      (fun a' -> gcd (modulo b (Pervasives.succ a')) (Pervasives.succ a'))
      a

  (** val square : OCamlNativeInt.t -> OCamlNativeInt.t **)

  let square n0 =
    mul n0 n0

  (** val sqrt_iter :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t ->
      OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec sqrt_iter k p q r =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        sqrt_iter k' (Pervasives.succ p) (Pervasives.succ (Pervasives.succ
          q)) (Pervasives.succ (Pervasives.succ q)))
        (fun r' -> sqrt_iter k' p q r')
        r)
      k

  (** val sqrt : OCamlNativeInt.t -> OCamlNativeInt.t **)

  let sqrt n0 =
    sqrt_iter n0 0 0 0

  (** val log2_iter :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t ->
      OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec log2_iter k p q r =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        log2_iter k' (Pervasives.succ p) (Pervasives.succ q) q)
        (fun r' -> log2_iter k' p (Pervasives.succ q) r')
        r)
      k

  (** val log2 : OCamlNativeInt.t -> OCamlNativeInt.t **)

  let log2 n0 =
    log2_iter (pred n0) 0 (Pervasives.succ 0) 0

  (** val iter : OCamlNativeInt.t -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n0 f x =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun n1 -> f (iter n1 f x))
      n0

  (** val div2 : OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec div2 = fun n -> n/2

  (** val testbit : OCamlNativeInt.t -> OCamlNativeInt.t -> bool **)

  let rec testbit a n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> odd a)
      (fun n1 -> testbit (div2 a) n1)
      n0

  (** val shiftl :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec shiftl a n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n1 -> double (shiftl a n1))
      n0

  (** val shiftr :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec shiftr a n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> a)
      (fun n1 -> div2 (shiftr a n1))
      n0

  (** val bitwise :
      (bool -> bool -> bool) -> OCamlNativeInt.t -> OCamlNativeInt.t ->
      OCamlNativeInt.t -> OCamlNativeInt.t **)

  let rec bitwise op n0 a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      add (if op (odd a) (odd b) then Pervasives.succ 0 else 0)
        (mul (Pervasives.succ (Pervasives.succ 0))
          (bitwise op n' (div2 a) (div2 b))))
      n0

  (** val coq_land :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let coq_land a b =
    bitwise (&&) a a b

  (** val coq_lor :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let coq_lor a b =
    bitwise (||) (max a b) a b

  (** val ldiff : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let ldiff a b =
    bitwise (fun b0 b' -> (&&) b0 (negb b')) a a b

  (** val coq_lxor :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let coq_lxor a b =
    bitwise xorb (max a b) a b

  (** val recursion :
      'a1 -> (OCamlNativeInt.t -> 'a1 -> 'a1) -> OCamlNativeInt.t -> 'a1 **)

  let rec recursion x f n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun n1 -> f n1 (recursion x f n1))
      n0

  (** val leb_spec0 : OCamlNativeInt.t -> OCamlNativeInt.t -> reflect **)

  let leb_spec0 x y =
    iff_reflect ((<=) x y)

  (** val ltb_spec0 : OCamlNativeInt.t -> OCamlNativeInt.t -> reflect **)

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

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        OCamlNativeInt.t -> OCamlNativeInt.t -> (OCamlNativeInt.t ->
        OCamlNativeInt.t -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)

    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))

    (** val max_case :
        OCamlNativeInt.t -> OCamlNativeInt.t -> (OCamlNativeInt.t ->
        OCamlNativeInt.t -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : OCamlNativeInt.t -> OCamlNativeInt.t -> bool **)

    let max_dec n0 m =
      max_case n0 m (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        OCamlNativeInt.t -> OCamlNativeInt.t -> (OCamlNativeInt.t ->
        OCamlNativeInt.t -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)

    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))

    (** val min_case :
        OCamlNativeInt.t -> OCamlNativeInt.t -> (OCamlNativeInt.t ->
        OCamlNativeInt.t -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : OCamlNativeInt.t -> OCamlNativeInt.t -> bool **)

    let min_dec n0 m =
      min_case n0 m (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong :
      OCamlNativeInt.t -> OCamlNativeInt.t -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1 **)

  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun _ _ _ x1 -> x1) x x0

  (** val max_case :
      OCamlNativeInt.t -> OCamlNativeInt.t -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : OCamlNativeInt.t -> OCamlNativeInt.t -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      OCamlNativeInt.t -> OCamlNativeInt.t -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1 **)

  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun _ _ _ x1 -> x1) x x0

  (** val min_case :
      OCamlNativeInt.t -> OCamlNativeInt.t -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : OCamlNativeInt.t -> OCamlNativeInt.t -> bool **)

  let min_dec =
    Private_Dec.min_dec

  module Private_Parity =
   struct
   end

  module Private_NZPow =
   struct
   end

  module Private_NZSqrt =
   struct
   end

  (** val sqrt_up : OCamlNativeInt.t -> OCamlNativeInt.t **)

  let sqrt_up a =
    match compare 0 a with
    | Lt -> Pervasives.succ (sqrt (pred a))
    | _ -> 0

  (** val log2_up : OCamlNativeInt.t -> OCamlNativeInt.t **)

  let log2_up a =
    match compare (Pervasives.succ 0) a with
    | Lt -> Pervasives.succ (log2 (pred a))
    | _ -> 0

  module Private_NZDiv =
   struct
   end

  (** val lcm : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let lcm a b =
    mul a (div b (gcd a b))

  (** val eqb_spec : OCamlNativeInt.t -> OCamlNativeInt.t -> reflect **)

  let eqb_spec x y =
    iff_reflect ((=) x y)

  (** val b2n : bool -> OCamlNativeInt.t **)

  let b2n = function
  | true -> Pervasives.succ 0
  | false -> 0

  (** val setbit :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let setbit a n0 =
    coq_lor a (shiftl (Pervasives.succ 0) n0)

  (** val clearbit :
      OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let clearbit a n0 =
    ldiff a (shiftl (Pervasives.succ 0) n0)

  (** val ones : OCamlNativeInt.t -> OCamlNativeInt.t **)

  let ones n0 =
    pred (shiftl (Pervasives.succ 0) n0)

  (** val lnot : OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t **)

  let lnot a n0 =
    coq_lxor a (ones n0)
 end

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

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
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
    | XH -> (match y with
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

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

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
    | XH -> (match y with
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

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module N =
 struct
  (** val succ : n -> n **)

  let succ = function
  | N0 -> Npos XH
  | Npos p -> Npos (Coq_Pos.succ p)

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
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Coq_Pos.mul p q))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Coq_Pos.compare n' m')
 end

module Z =
 struct
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

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

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

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val pos_div_eucl : positive -> z -> z*z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let q,r = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then (mul (Zpos (XO XH)) q),r'
      else (add (mul (Zpos (XO XH)) q) (Zpos XH)),(sub r' b)
    | XO a' ->
      let q,r = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then (mul (Zpos (XO XH)) q),r'
      else (add (mul (Zpos (XO XH)) q) (Zpos XH)),(sub r' b)
    | XH -> if leb (Zpos (XO XH)) b then Z0,(Zpos XH) else (Zpos XH),Z0

  (** val div_eucl : z -> z -> z*z **)

  let div_eucl a b =
    match a with
    | Z0 -> Z0,Z0
    | Zpos a' ->
      (match b with
       | Z0 -> Z0,Z0
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let q,r = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> (opp q),Z0
          | _ -> (opp (add q (Zpos XH))),(add b r)))
    | Zneg a' ->
      (match b with
       | Z0 -> Z0,Z0
       | Zpos _ ->
         let q,r = pos_div_eucl a' b in
         (match r with
          | Z0 -> (opp q),Z0
          | _ -> (opp (add q (Zpos XH))),(sub b r))
       | Zneg b' -> let q,r = pos_div_eucl a' (Zpos b') in q,(opp r))

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let _,r = div_eucl a b in r
 end

(** val pow2 : OCamlNativeInt.t -> OCamlNativeInt.t **)

let rec pow2 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Pervasives.succ 0)
    (fun n' -> mul (Pervasives.succ (Pervasives.succ 0)) (pow2 n'))
    n0



module Coq_Nat = Nat

(** val if_Then_Else : bool -> 'a1 -> 'a1 -> 'a1 **)

let if_Then_Else c t0 e =
  if c then t0 else e

type 'a indexBound =
  ArrayVector.idx_t
  (* singleton inductive, whose constructor was Build_IndexBound *)

(** val ibound :
    OCamlNativeInt.t -> 'a1 -> 'a1 StackVector.t -> 'a1 indexBound ->
    ArrayVector.idx_t **)

let ibound _ _ _ indexBound0 =
  indexBound0

type 'a boundedIndex = { bindex : 'a; indexb : 'a indexBound }

(** val bindex :
    OCamlNativeInt.t -> 'a1 StackVector.t -> 'a1 boundedIndex -> 'a1 **)

let bindex _ _ x = x.bindex

(** val indexb :
    OCamlNativeInt.t -> 'a1 StackVector.t -> 'a1 boundedIndex -> 'a1
    indexBound **)

let indexb _ _ x = x.indexb

type 'a enumType = ArrayVector.idx_t

(** val boundedIndex_inj_EnumType :
    OCamlNativeInt.t -> 'a1 StackVector.t -> 'a1 boundedIndex -> 'a1 enumType **)

let boundedIndex_inj_EnumType len ta idx =
  ibound (Pervasives.succ len) idx.bindex ta idx.indexb

type cache =
| Build_Cache

type cacheFormat = __

type cacheDecode = __

type 't cacheAdd = { addE : (cacheFormat -> 't -> cacheFormat);
                     addD : (cacheDecode -> 't -> cacheDecode) }

(** val addE : cache -> 'a1 cacheAdd -> cacheFormat -> 'a1 -> cacheFormat **)

let addE _ x = x.addE

(** val addD : cache -> 'a1 cacheAdd -> cacheDecode -> 'a1 -> cacheDecode **)

let addD _ x = x.addD

type char = Int64Word.t



module ByteBuffer =
 struct
 end

type 's alignedEncodeM =
  CstructBytestring.storage_t -> OCamlNativeInt.t -> 's -> cacheFormat ->
  ((CstructBytestring.storage_t*OCamlNativeInt.t)*cacheFormat) option

(** val alignedEncode_Nil :
    cache -> OCamlNativeInt.t -> 'a1 alignedEncodeM **)

let alignedEncode_Nil _ numBytes v idx _ env =
  if Nat.ltb idx (Pervasives.succ numBytes) then Some ((v,idx),env) else None

(** val setByteAt :
    cache -> OCamlNativeInt.t cacheAdd -> OCamlNativeInt.t ->
    OCamlNativeInt.t -> char alignedEncodeM **)

let setByteAt _ cacheAddNat n0 idx' v _ s ce =
  if (<) idx' n0
  then Some (((CstructBytestring.set_nth n0 v idx' s),(Pervasives.succ
         idx')),(cacheAddNat.addE ce (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  0))))))))))
  else None

type 'a alignedDecodeM =
  CstructBytestring.storage_t -> OCamlNativeInt.t -> cacheDecode ->
  (('a*OCamlNativeInt.t)*cacheDecode) option

(** val skipCurrentByte :
    cache -> OCamlNativeInt.t cacheAdd -> OCamlNativeInt.t -> unit
    alignedDecodeM **)

let skipCurrentByte _ cacheAddNat n0 v idx c =
  match CstructBytestring.nth_opt n0 v idx with
  | Some _ ->
    Some (((),(Pervasives.succ
      idx)),(cacheAddNat.addD c (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))
  | None -> None

(** val getCurrentBytes :
    cache -> OCamlNativeInt.t cacheAdd -> OCamlNativeInt.t ->
    OCamlNativeInt.t -> Int64Word.t alignedDecodeM **)

let rec getCurrentBytes cache0 cacheAddNat n0 m v idx c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some (((Int64Word.w0),idx),c))
    (fun m' ->
    match CstructBytestring.nth_opt n0 v idx with
    | Some a ->
      let a0 = (a,(Pervasives.succ
        idx)),(cacheAddNat.addD c (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))
      in
      (match getCurrentBytes cache0 cacheAddNat n0 m' v
               (let _,y = let x,_ = a0 in x in y) (let _,y = a0 in y) with
       | Some a1 ->
         Some
           (((Int64Word.append
               (mul m' (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ 0)))))))))
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ 0))))))))
               (let x,_ = let x,_ = a1 in x in x)
               (let x,_ = let x,_ = a0 in x in x)),(let _,y =
                                                      let x,_ = a1 in x
                                                    in
                                                    y)),(let _,y = a1 in y))
       | None -> None)
    | None -> None)
    m

(** val setCurrentBytes :
    cache -> OCamlNativeInt.t cacheAdd -> OCamlNativeInt.t ->
    OCamlNativeInt.t -> Int64Word.t alignedEncodeM **)

let rec setCurrentBytes cache0 cacheAddNat n0 sz =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> alignedEncode_Nil cache0 n0)
    (fun sz0 v idx w ce ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      if Nat.ltb idx n0
      then Some (((CstructBytestring.set_nth n0 v idx w),(Pervasives.succ
             idx)),(cacheAddNat.addE ce (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     0))))))))))
      else None)
      (fun _ ->
      if Nat.ltb idx n0
      then let a =
             ((CstructBytestring.set_nth n0 v idx
                (Int64Word.split1' (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  0))))))))
                  (mul sz0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ 0))))))))) w)),(Pervasives.succ
             idx)),(cacheAddNat.addE ce (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     0)))))))))
           in
           setCurrentBytes cache0 cacheAddNat n0 sz0
             (let x,_ = let x,_ = a in x in x)
             (let _,y = let x,_ = a in x in y)
             (Int64Word.split2' (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
               (mul sz0 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ 0))))))))) w)
             (let _,y = a in y)
      else None)
      sz0)
    sz

(** val test_cache : cache **)

let test_cache =
  Build_Cache

(** val test_cache_add_nat : OCamlNativeInt.t cacheAdd **)

let test_cache_add_nat =
  { addE = (fun ce _ -> ce); addD = (fun cd _ -> cd) }

type w16 = Int64Word.t

(** val oneC_plus :
    OCamlNativeInt.t -> Int64Word.t -> Int64Word.t -> Int64Word.t **)

let oneC_plus = Int64Word.onec_plus

(** val byteBuffer_checksum :
    OCamlNativeInt.t -> CstructBytestring.storage_t -> w16 **)

let byteBuffer_checksum sz bytes =
  CstructBytestring.checksum_bound sz sz bytes

(** val alignedEncodeVector' :
    cache -> OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t ->
    (OCamlNativeInt.t -> 'a1 alignedEncodeM) -> OCamlNativeInt.t ->
    CstructBytestring.storage_t -> OCamlNativeInt.t -> 'a1 StackVector.t ->
    cacheFormat ->
    ((CstructBytestring.storage_t*OCamlNativeInt.t)*cacheFormat) option **)

let rec alignedEncodeVector' cache0 n0 n' sz s_format_align numBytes v idx ss env =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    if (<) idx (add (Pervasives.succ 0) numBytes)
    then Some ((v,idx),env)
    else None)
    (fun n'' ->
    match StackVector.nth_opt sz ss n' with
    | Some a ->
      (match s_format_align numBytes v idx a env with
       | Some a0 ->
         alignedEncodeVector' cache0 n'' (add (Pervasives.succ 0) n') sz
           s_format_align numBytes (let x,_ = let x,_ = a0 in x in x)
           (let _,y = let x,_ = a0 in x in y) ss (let _,y = a0 in y)
       | None -> None)
    | None -> None)
    n0

(** val alignedEncodeVector :
    cache -> OCamlNativeInt.t -> (OCamlNativeInt.t -> 'a1 alignedEncodeM) ->
    OCamlNativeInt.t -> 'a1 StackVector.t alignedEncodeM **)

let alignedEncodeVector cache0 sz s_format_align =
  alignedEncodeVector' cache0 sz 0 sz s_format_align

(** val aligned_option_encode :
    cache -> (OCamlNativeInt.t -> 'a1 alignedEncodeM) -> (OCamlNativeInt.t ->
    unit alignedEncodeM) -> OCamlNativeInt.t -> 'a1 option alignedEncodeM **)

let aligned_option_encode _ encode_Some encode_None sz v idx = function
| Some a -> encode_Some sz v idx a
| None -> encode_None sz v idx ()

(** val aligned_decode_enum :
    OCamlNativeInt.t -> cache -> OCamlNativeInt.t cacheAdd -> Int64Word.t
    StackVector.t -> OCamlNativeInt.t -> ArrayVector.idx_t alignedDecodeM **)

let aligned_decode_enum len _ cacheAddNat tb n0 v idx c =
  match CstructBytestring.nth_opt n0 v idx with
  | Some a ->
    let a0 = (a,(Pervasives.succ
      idx)),(cacheAddNat.addD c (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))
    in
    (match StackVector.index (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
             (Pervasives.succ len) (let x,_ = let x,_ = a0 in x in x) tb with
     | Some a1 ->
       Some ((a1,(let _,y = let x,_ = a0 in x in y)),(let _,y = a0 in y))
     | None -> None)
  | None -> None

(** val aligned_decode_enumN :
    OCamlNativeInt.t -> OCamlNativeInt.t -> cache -> OCamlNativeInt.t
    cacheAdd -> Int64Word.t StackVector.t -> OCamlNativeInt.t ->
    ArrayVector.idx_t alignedDecodeM **)

let aligned_decode_enumN sz len cache0 cacheAddNat tb n0 v idx c =
  match getCurrentBytes cache0 cacheAddNat n0 sz v idx c with
  | Some a ->
    (match StackVector.index
             (mul sz (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ (Pervasives.succ
               (Pervasives.succ (Pervasives.succ 0))))))))) (Pervasives.succ
             len) (let x,_ = let x,_ = a in x in x) tb with
     | Some a0 ->
       Some ((a0,(let _,y = let x,_ = a in x in y)),(let _,y = a in y))
     | None -> None)
  | None -> None

(** val aligned_option_decode :
    cache -> (OCamlNativeInt.t -> 'a1 alignedDecodeM) -> (OCamlNativeInt.t ->
    unit alignedDecodeM) -> bool -> OCamlNativeInt.t -> 'a1 option
    alignedDecodeM **)

let aligned_option_decode _ decode_Some decode_None b' sz v idx env =
  if_Then_Else b'
    (match decode_Some sz v idx env with
     | Some p -> let p0,c = p in let a,b = p0 in Some (((Some a),b),c)
     | None -> None)
    (match decode_None sz v idx env with
     | Some p -> let p0,c = p in let _,b = p0 in Some ((None,b),c)
     | None -> None)

(** val listAlignedDecodeM :
    cache -> OCamlNativeInt.t -> (OCamlNativeInt.t -> 'a1 alignedDecodeM) ->
    OCamlNativeInt.t -> 'a1 list alignedDecodeM **)

let rec listAlignedDecodeM cache0 m a_decode_align n0 x x0 x1 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some (([],x0),x1))
    (fun s' ->
    match a_decode_align m x x0 x1 with
    | Some a ->
      (match listAlignedDecodeM cache0 m a_decode_align s' x
               (let _,y = let x2,_ = a in x2 in y) (let _,y = a in y) with
       | Some a0 ->
         Some
           ((((let x2,_ = let x2,_ = a in x2 in x2) :: (let x2,_ =
                                                          let x2,_ = a0 in x2
                                                        in
                                                        x2)),(let _,y =
                                                                let x2,_ = a0
                                                                in
                                                                x2
                                                              in
                                                              y)),(let _,y =
                                                                    a0
                                                                   in
                                                                   y))
       | None -> None)
    | None -> None)
    n0

(** val bytebuffer_of_bytebuffer_range :
    OCamlNativeInt.t -> OCamlNativeInt.t -> OCamlNativeInt.t ->
    CstructBytestring.storage_t -> (OCamlNativeInt.t,
    CstructBytestring.storage_t) sigT **)

let bytebuffer_of_bytebuffer_range = (fun sz from len v ->
    let b = CstructBytestring.slice_range sz from len v in
    ExistT (CstructBytestring.length b, b))

(** val byteBufferAlignedDecodeM :
    cache -> OCamlNativeInt.t cacheAdd -> OCamlNativeInt.t ->
    OCamlNativeInt.t -> (OCamlNativeInt.t, CstructBytestring.storage_t) sigT
    alignedDecodeM **)

let byteBufferAlignedDecodeM _ cacheAddNat m len v idx env =
  let lastidx = add idx len in
  if (<=) lastidx m
  then Some
         (((bytebuffer_of_bytebuffer_range m idx len v),lastidx),(cacheAddNat.addD
                                                                   env
                                                                   (mul
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    len)))
  else None

(** val alignedEncodeList' :
    cache -> (OCamlNativeInt.t -> 'a1 alignedEncodeM) -> OCamlNativeInt.t ->
    CstructBytestring.storage_t -> OCamlNativeInt.t -> 'a1 list ->
    cacheFormat ->
    ((CstructBytestring.storage_t*OCamlNativeInt.t)*cacheFormat) option **)

let rec alignedEncodeList' cache0 a_format_align sz v idx as0 env =
  match as0 with
  | [] -> if (<) idx (Pervasives.succ sz) then Some ((v,idx),env) else None
  | a :: as' ->
    (match a_format_align sz v idx a env with
     | Some a0 ->
       alignedEncodeList' cache0 a_format_align sz
         (let x,_ = let x,_ = a0 in x in x)
         (let _,y = let x,_ = a0 in x in y) as' (let _,y = a0 in y)
     | None -> None)

(** val alignedEncodeByteBuffer :
    cache -> OCamlNativeInt.t cacheAdd -> OCamlNativeInt.t ->
    (OCamlNativeInt.t, CstructBytestring.storage_t) sigT alignedEncodeM **)

let alignedEncodeByteBuffer _ cacheAddNat sz2 dst idx src env =
  let ExistT (len, src0) = src in
  (match CstructBytestring.blit_buffer len sz2 idx src0 dst with
   | Some p ->
     Some
       (p,(cacheAddNat.addE env
            (mul (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0)))))))) len)))
   | None -> None)

(** val alignedEncodeList :
    cache -> (OCamlNativeInt.t -> 'a1 alignedEncodeM) -> OCamlNativeInt.t ->
    'a1 list alignedEncodeM **)

let alignedEncodeList =
  alignedEncodeList'

(** val calculate_IPChecksum : OCamlNativeInt.t -> 'a1 alignedEncodeM **)

let calculate_IPChecksum sz v =
  let checksum =
    CstructBytestring.checksum_bound (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))) sz v
  in
  (fun _ _ c ->
  match setByteAt test_cache test_cache_add_nat sz (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))))))))) v 0
          (Int64Word.wnot (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ 0))))))))
            (Int64Word.split2 (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0)))))))) checksum)) c with
  | Some a ->
    setByteAt test_cache test_cache_add_nat sz (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))))))
      (let x,_ = let x,_ = a in x in x) 0
      (Int64Word.wnot (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))
        (Int64Word.split1 (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))))))) (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))) checksum))
      (let _,y = a in y)
  | None -> None)

(** val pseudoHeader_checksum' :
    Int64Word.t StackVector.t -> Int64Word.t StackVector.t -> Int64Word.t ->
    Int64Word.t -> OCamlNativeInt.t -> CstructBytestring.storage_t ->
    Int64Word.t **)

let pseudoHeader_checksum' srcAddr destAddr udpLength protoCode sz packet =
  oneC_plus (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))))
    (oneC_plus (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))))))
      (oneC_plus (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))))))))))
        (oneC_plus (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0))))))))))))))))
          (byteBuffer_checksum (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ 0)))) srcAddr)
          (byteBuffer_checksum (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ 0)))) destAddr))
        (Int64Word.zext (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))))))) protoCode (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))
      udpLength)
    (CstructBytestring.checksum_bound
      (Int64Word.wordToNat (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0)))))))))))))))) udpLength) sz packet)

(** val calculate_PseudoChecksum :
    OCamlNativeInt.t -> Int64Word.t StackVector.t -> Int64Word.t
    StackVector.t -> Int64Word.t -> Int64Word.t -> OCamlNativeInt.t -> 'a1
    alignedEncodeM **)

let calculate_PseudoChecksum sz srcAddr destAddr udpLength protoCode idx' v _ _ =
  let checksum =
    pseudoHeader_checksum' srcAddr destAddr udpLength protoCode sz v
  in
  (fun c ->
  match setByteAt test_cache test_cache_add_nat sz idx' v 0
          (Int64Word.wnot (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ 0))))))))
            (Int64Word.split2 (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0)))))))) checksum)) c with
  | Some a ->
    setByteAt test_cache test_cache_add_nat sz (add (Pervasives.succ 0) idx')
      (let x,_ = let x,_ = a in x in x) 0
      (Int64Word.wnot (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))))))
        (Int64Word.split1 (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ 0)))))))) (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ 0)))))))) checksum))
      (let _,y = a in y)
  | None -> None)

type ethernetHeader = { destination : Int64Word.t StackVector.t;
                        source : Int64Word.t StackVector.t;
                        ethType : char list enumType }

(** val destination : ethernetHeader -> Int64Word.t StackVector.t **)

let destination x = x.destination

(** val source : ethernetHeader -> Int64Word.t StackVector.t **)

let source x = x.source

(** val ethType : ethernetHeader -> char list enumType **)

let ethType x = x.ethType

(** val etherTypeCodes : Int64Word.t StackVector.t **)

let etherTypeCodes =
  StackVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))), (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (StackVector.cons ((Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))), (Pervasives.succ
    (Pervasives.succ 0)), (StackVector.cons ((Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (true, 0, (Int64Word.w0))))))))))))))))))))))))))))))))),
    (Pervasives.succ 0), (StackVector.cons ((Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))))))))))))))))))),
    0, StackVector.empty ())))))))

(** val ethernetHeader_encoder_impl :
    ethernetHeader -> OCamlNativeInt.t -> CstructBytestring.storage_t ->
    ((CstructBytestring.storage_t*OCamlNativeInt.t)*cacheFormat) option **)

let ethernetHeader_encoder_impl r sz v =
  match alignedEncodeVector test_cache (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0)))))) (fun n0 v0 idx s ce ->
          if Nat.ltb idx n0
          then Some
                 (((CstructBytestring.set_nth n0 v0 idx s),(Pervasives.succ
                 idx)),(test_cache_add_nat.addE ce (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ 0))))))))))
          else None) sz v 0 r.destination (Obj.magic ()) with
  | Some a ->
    (match alignedEncodeVector test_cache (Pervasives.succ (Pervasives.succ
             (Pervasives.succ (Pervasives.succ (Pervasives.succ
             (Pervasives.succ 0)))))) (fun n0 v0 idx s ce ->
             if Nat.ltb idx n0
             then Some
                    (((CstructBytestring.set_nth n0 v0 idx s),(Pervasives.succ
                    idx)),(test_cache_add_nat.addE ce (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ 0))))))))))
             else None) sz (let x,_ = let x,_ = a in x in x)
             (let _,y = let x,_ = a in x in y) r.source (let _,y = a in y) with
     | Some a0 ->
       setCurrentBytes test_cache test_cache_add_nat sz (Pervasives.succ
         (Pervasives.succ 0)) (let x,_ = let x,_ = a0 in x in x)
         (let _,y = let x,_ = a0 in x in y)
         (StackVector.nth (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ 0)))) etherTypeCodes r.ethType)
         (let _,y = a0 in y)
     | None -> None)
  | None -> None

(** val aligned_v1042_test :
    OCamlNativeInt.t -> char StackVector.t -> OCamlNativeInt.t -> bool **)

let aligned_v1042_test sz v idx =
  match CstructBytestring.nth_opt sz v idx with
  | Some w1 ->
    (match CstructBytestring.nth_opt sz v (Pervasives.succ idx) with
     | Some w2 ->
       if Int64Word.wlt_dec
            (add (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0)))))))) (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ 0)))))))))
            (Int64Word.combine (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))) w2
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0)))))))) w1)
            (Int64Word.natToWord (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ 0))))))))))))))))
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ
              0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       then true
       else false
     | None -> false)
  | None -> false

(** val ethernet_decoder_impl :
    OCamlNativeInt.t -> OCamlNativeInt.t -> CstructBytestring.storage_t ->
    ((ethernetHeader*OCamlNativeInt.t)*cacheDecode) option **)

let ethernet_decoder_impl packet_len sz v =
  match let idx = 0 in
        (match CstructBytestring.nth_opt sz v idx with
         | Some a ->
           Some ((a,(Pervasives.succ
             idx)),(test_cache_add_nat.addD (Obj.magic ()) (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ 0))))))))))
         | None -> None) with
  | Some a ->
    let idx = let _,y = let x,_ = a in x in y in
    (match CstructBytestring.nth_opt sz v idx with
     | Some a0 ->
       let a1 = (a0,(Pervasives.succ
         idx)),(test_cache_add_nat.addD (let _,y = a in y) (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ (Pervasives.succ (Pervasives.succ
                 (Pervasives.succ 0)))))))))
       in
       let idx0 = let _,y = let x,_ = a1 in x in y in
       (match CstructBytestring.nth_opt sz v idx0 with
        | Some a2 ->
          let a3 = (a2,(Pervasives.succ
            idx0)),(test_cache_add_nat.addD (let _,y = a1 in y)
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ 0)))))))))
          in
          let idx1 = let _,y = let x,_ = a3 in x in y in
          (match CstructBytestring.nth_opt sz v idx1 with
           | Some a4 ->
             let a5 = (a4,(Pervasives.succ
               idx1)),(test_cache_add_nat.addD (let _,y = a3 in y)
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ 0)))))))))
             in
             let idx2 = let _,y = let x,_ = a5 in x in y in
             (match CstructBytestring.nth_opt sz v idx2 with
              | Some a6 ->
                let a7 = (a6,(Pervasives.succ
                  idx2)),(test_cache_add_nat.addD (let _,y = a5 in y)
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ 0)))))))))
                in
                let idx3 = let _,y = let x,_ = a7 in x in y in
                (match CstructBytestring.nth_opt sz v idx3 with
                 | Some a8 ->
                   let a9 = (a8,(Pervasives.succ
                     idx3)),(test_cache_add_nat.addD (let _,y = a7 in y)
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ 0)))))))))
                   in
                   let idx4 = let _,y = let x,_ = a9 in x in y in
                   (match CstructBytestring.nth_opt sz v idx4 with
                    | Some a10 ->
                      let a11 = (a10,(Pervasives.succ
                        idx4)),(test_cache_add_nat.addD (let _,y = a9 in y)
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ 0)))))))))
                      in
                      let idx5 = let _,y = let x,_ = a11 in x in y in
                      (match CstructBytestring.nth_opt sz v idx5 with
                       | Some a12 ->
                         let a13 = (a12,(Pervasives.succ
                           idx5)),(test_cache_add_nat.addD
                                    (let _,y = a11 in y) (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0)))))))))
                         in
                         let idx6 = let _,y = let x,_ = a13 in x in y in
                         (match CstructBytestring.nth_opt sz v idx6 with
                          | Some a14 ->
                            let a15 = (a14,(Pervasives.succ
                              idx6)),(test_cache_add_nat.addD
                                       (let _,y = a13 in y) (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ 0)))))))))
                            in
                            let idx7 = let _,y = let x,_ = a15 in x in y in
                            (match CstructBytestring.nth_opt sz v idx7 with
                             | Some a16 ->
                               let a17 = (a16,(Pervasives.succ
                                 idx7)),(test_cache_add_nat.addD
                                          (let _,y = a15 in y)
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0)))))))))
                               in
                               let idx8 = let _,y = let x,_ = a17 in x in y in
                               (match CstructBytestring.nth_opt sz v idx8 with
                                | Some a18 ->
                                  let a19 = (a18,(Pervasives.succ
                                    idx8)),(test_cache_add_nat.addD
                                             (let _,y = a17 in y)
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0)))))))))
                                  in
                                  let idx9 = let _,y = let x,_ = a19 in x in y
                                  in
                                  (match CstructBytestring.nth_opt sz v idx9 with
                                   | Some a20 ->
                                     let a21 = (a20,(Pervasives.succ
                                       idx9)),(test_cache_add_nat.addD
                                                (let _,y = a19 in y)
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0)))))))))
                                     in
                                     let idx10 =
                                       let _,y = let x,_ = a21 in x in y
                                     in
                                     let c = let _,y = a21 in y in
                                     if aligned_v1042_test sz v idx10
                                     then (match CstructBytestring.nth_opt sz
                                                   v idx10 with
                                           | Some a22 ->
                                             let a23 = (a22,(Pervasives.succ
                                               idx10)),(test_cache_add_nat.addD
                                                         c (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         0)))))))))
                                             in
                                             let idx11 =
                                               let _,y = let x,_ = a23 in x in
                                               y
                                             in
                                             (match CstructBytestring.nth_opt
                                                      sz v idx11 with
                                              | Some a24 ->
                                                let a25 =
                                                  (a24,(Pervasives.succ
                                                  idx11)),(test_cache_add_nat.addD
                                                            (let _,y = a23 in
                                                             y)
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0)))))))))
                                                in
                                                let a26 =
                                                  ((Int64Word.append
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     0))))))))
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     0))))))))
                                                     (let x,_ =
                                                        let x,_ = a25 in x
                                                      in
                                                      x)
                                                     (let x,_ =
                                                        let x,_ = a23 in x
                                                      in
                                                      x)),(let _,y =
                                                             let x,_ = a25 in
                                                             x
                                                           in
                                                           y)),(let _,y = a25
                                                                in
                                                                y)
                                                in
                                                let idx12 =
                                                  let _,y = let x,_ = a26 in x
                                                  in
                                                  y
                                                in
                                                let c0 = let _,y = a26 in y in
                                                if (=)
                                                     (Int64Word.wordToNat
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
                                                       (Pervasives.succ
                                                       0))))))))))))))))
                                                       (let x,_ =
                                                          let x,_ = a26 in x
                                                        in
                                                        x)) packet_len
                                                then (match CstructBytestring.nth_opt
                                                              sz v idx12 with
                                                      | Some a27 ->
                                                        let a28 =
                                                          (a27,(Pervasives.succ
                                                          idx12)),(test_cache_add_nat.addD
                                                                    c0
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                        in
                                                        let idx13 =
                                                          let _,y =
                                                            let x,_ = a28 in x
                                                          in
                                                          y
                                                        in
                                                        let c1 =
                                                          let _,y = a28 in y
                                                        in
                                                        if Int64Word.weq
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             0))))))))
                                                             (let x,_ =
                                                                let x,_ = a28
                                                                in
                                                                x
                                                              in
                                                              x)
                                                             (Int64Word.ws
                                                             (true,
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             0))))))),
                                                             (Int64Word.ws
                                                             (false,
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             0)))))),
                                                             (Int64Word.ws
                                                             (true,
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             0))))),
                                                             (Int64Word.ws
                                                             (false,
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             0)))),
                                                             (Int64Word.ws
                                                             (true,
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             0))),
                                                             (Int64Word.ws
                                                             (false,
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             0)),
                                                             (Int64Word.ws
                                                             (true,
                                                             (Pervasives.succ
                                                             0),
                                                             (Int64Word.ws
                                                             (false, 0,
                                                             (Int64Word.w0)))))))))))))))))
                                                        then (match CstructBytestring.nth_opt
                                                                    sz v idx13 with
                                                              | Some a29 ->
                                                                let a30 =
                                                                  (a29,(Pervasives.succ
                                                                  idx13)),
                                                                  (test_cache_add_nat.addD
                                                                    c1
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                in
                                                                let idx14 =
                                                                  let _,y =
                                                                    let x,_ =
                                                                    a30
                                                                    in
                                                                    x
                                                                  in
                                                                  y
                                                                in
                                                                let c2 =
                                                                  let _,y =
                                                                    a30
                                                                  in
                                                                  y
                                                                in
                                                                if Int64Word.weq
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a30
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (Int64Word.ws
                                                                    (true,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))),
                                                                    (Int64Word.ws
                                                                    (false,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))),
                                                                    (Int64Word.ws
                                                                    (true,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))),
                                                                    (Int64Word.ws
                                                                    (false,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))),
                                                                    (Int64Word.ws
                                                                    (true,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))),
                                                                    (Int64Word.ws
                                                                    (false,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)),
                                                                    (Int64Word.ws
                                                                    (true,
                                                                    (Pervasives.succ
                                                                    0),
                                                                    (Int64Word.ws
                                                                    (false,
                                                                    0,
                                                                    (Int64Word.w0)))))))))))))))))
                                                                then 
                                                                  (match 
                                                                   CstructBytestring.nth_opt
                                                                    sz v idx14 with
                                                                   | Some a31 ->
                                                                    let a32 =
                                                                    (a31,(Pervasives.succ
                                                                    idx14)),
                                                                    (test_cache_add_nat.addD
                                                                    c2
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let idx15 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a32
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    let c3 =
                                                                    let _,y =
                                                                    a32
                                                                    in
                                                                    y
                                                                    in
                                                                    if 
                                                                    Int64Word.weq
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a32
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (Int64Word.ws
                                                                    (false,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))),
                                                                    (Int64Word.ws
                                                                    (false,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))),
                                                                    (Int64Word.ws
                                                                    (false,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))),
                                                                    (Int64Word.ws
                                                                    (false,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))),
                                                                    (Int64Word.ws
                                                                    (false,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))),
                                                                    (Int64Word.ws
                                                                    (false,
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)),
                                                                    (Int64Word.ws
                                                                    (true,
                                                                    (Pervasives.succ
                                                                    0),
                                                                    (Int64Word.ws
                                                                    (true, 0,
                                                                    (Int64Word.w0)))))))))))))))))
                                                                    then 
                                                                    (match 
                                                                    CstructBytestring.nth_opt
                                                                    sz v idx15 with
                                                                    | Some a33 ->
                                                                    let a34 =
                                                                    (a33,(Pervasives.succ
                                                                    idx15)),
                                                                    (test_cache_add_nat.addD
                                                                    c3
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let idx16 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a34
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    (
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    sz v idx16 with
                                                                    | Some a35 ->
                                                                    let a36 =
                                                                    (a35,(Pervasives.succ
                                                                    idx16)),
                                                                    (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a34
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let idx17 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a36
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    (
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    sz v idx17 with
                                                                    | Some a37 ->
                                                                    let a38 =
                                                                    (a37,(Pervasives.succ
                                                                    idx17)),
                                                                    (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a36
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let a39 =
                                                                    ((Int64Word.append
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (add
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a38
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (Int64Word.append
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a36
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a34
                                                                    in
                                                                    x
                                                                    in
                                                                    x))),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a38
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a38
                                                                    in
                                                                    y)
                                                                    in
                                                                    let idx18 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a39
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    let c4 =
                                                                    let _,y =
                                                                    a39
                                                                    in
                                                                    y
                                                                    in
                                                                    if 
                                                                    Int64Word.weq
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
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))))))))))))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a39
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (Int64Word.wzero
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
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))))))))))))))))))
                                                                    then 
                                                                    (match 
                                                                    aligned_decode_enumN
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    test_cache
                                                                    test_cache_add_nat
                                                                    etherTypeCodes
                                                                    sz v
                                                                    idx18 c4 with
                                                                    | Some a40 ->
                                                                    Some
                                                                    (({ destination =
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a
                                                                    in
                                                                    x
                                                                    in
                                                                    x),
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))),
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a1
                                                                    in
                                                                    x
                                                                    in
                                                                    x),
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))),
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a3
                                                                    in
                                                                    x
                                                                    in
                                                                    x),
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))),
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a5
                                                                    in
                                                                    x
                                                                    in
                                                                    x),
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)),
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a7
                                                                    in
                                                                    x
                                                                    in
                                                                    x),
                                                                    (Pervasives.succ
                                                                    0),
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a9
                                                                    in
                                                                    x
                                                                    in
                                                                    x), 0,
                                                                    StackVector.empty ()))))))))))));
                                                                    source =
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a11
                                                                    in
                                                                    x
                                                                    in
                                                                    x),
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))),
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a13
                                                                    in
                                                                    x
                                                                    in
                                                                    x),
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))),
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a15
                                                                    in
                                                                    x
                                                                    in
                                                                    x),
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))),
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a17
                                                                    in
                                                                    x
                                                                    in
                                                                    x),
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)),
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a19
                                                                    in
                                                                    x
                                                                    in
                                                                    x),
                                                                    (Pervasives.succ
                                                                    0),
                                                                    (StackVector.cons
                                                                    ((
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a21
                                                                    in
                                                                    x
                                                                    in
                                                                    x), 0,
                                                                    StackVector.empty ()))))))))))));
                                                                    ethType =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a40
                                                                    in
                                                                    x
                                                                    in
                                                                    x) },
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a40
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a40
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None)
                                                                    else None
                                                                    | None ->
                                                                    None)
                                                                    | None ->
                                                                    None)
                                                                    | None ->
                                                                    None)
                                                                    else None
                                                                   | None ->
                                                                    None)
                                                                else None
                                                              | None -> None)
                                                        else None
                                                      | None -> None)
                                                else None
                                              | None -> None)
                                           | None -> None)
                                     else (match aligned_decode_enumN
                                                   (Pervasives.succ
                                                   (Pervasives.succ 0))
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ 0)))
                                                   test_cache
                                                   test_cache_add_nat
                                                   etherTypeCodes sz v idx10 c with
                                           | Some a22 ->
                                             Some (({ destination =
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a in x in
                                                 x), (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0))))),
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a1 in x
                                                 in
                                                 x), (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0)))),
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a3 in x
                                                 in
                                                 x), (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0))),
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a5 in x
                                                 in
                                                 x), (Pervasives.succ
                                               (Pervasives.succ 0)),
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a7 in x
                                                 in
                                                 x), (Pervasives.succ 0),
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a9 in x
                                                 in
                                                 x), 0,
                                               StackVector.empty ()))))))))))));
                                               source = (StackVector.cons
                                               ((let x,_ = let x,_ = a11 in x
                                                 in
                                                 x), (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0))))),
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a13 in x
                                                 in
                                                 x), (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0)))),
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a15 in x
                                                 in
                                                 x), (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0))),
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a17 in x
                                                 in
                                                 x), (Pervasives.succ
                                               (Pervasives.succ 0)),
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a19 in x
                                                 in
                                                 x), (Pervasives.succ 0),
                                               (StackVector.cons
                                               ((let x,_ = let x,_ = a21 in x
                                                 in
                                                 x), 0,
                                               StackVector.empty ()))))))))))));
                                               ethType =
                                               (let x,_ = let x,_ = a22 in x
                                                in
                                                x) },(let _,y =
                                                        let x,_ = a22 in x
                                                      in
                                                      y)),(let _,y = a22 in y))
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
  | None -> None

type aRPPacket = { hardType : char list enumType;
                   protType : char list enumType;
                   operation : char list enumType;
                   senderHardAddress : Int64Word.t list;
                   senderProtAddress : Int64Word.t list;
                   targetHardAddress : Int64Word.t list;
                   targetProtAddress : Int64Word.t list }

(** val hardType : aRPPacket -> char list enumType **)

let hardType x = x.hardType

(** val protType : aRPPacket -> char list enumType **)

let protType x = x.protType

(** val operation : aRPPacket -> char list enumType **)

let operation x = x.operation

(** val senderHardAddress : aRPPacket -> Int64Word.t list **)

let senderHardAddress x = x.senderHardAddress

(** val senderProtAddress : aRPPacket -> Int64Word.t list **)

let senderProtAddress x = x.senderProtAddress

(** val targetHardAddress : aRPPacket -> Int64Word.t list **)

let targetHardAddress x = x.targetHardAddress

(** val targetProtAddress : aRPPacket -> Int64Word.t list **)

let targetProtAddress x = x.targetProtAddress

(** val hardTypeCodes : Int64Word.t StackVector.t **)

let hardTypeCodes =
  StackVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))), (Pervasives.succ
    (Pervasives.succ 0)), (StackVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))))))))))))))))))),
    (Pervasives.succ 0), (StackVector.cons ((Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))))))))))))))))))),
    0, StackVector.empty ())))))

(** val etherTypeCodes0 : Int64Word.t StackVector.t **)

let etherTypeCodes0 =
  StackVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))), (Pervasives.succ 0),
    (StackVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (true, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))), 0, StackVector.empty ())))

(** val hardSizeCodes : Int64Word.t StackVector.t **)

let hardSizeCodes =
  StackVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ 0)),
    (StackVector.cons ((Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)),
    (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ 0), (StackVector.cons
    ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), 0, StackVector.empty ())))))

(** val protSizeCodes : Int64Word.t StackVector.t **)

let protSizeCodes =
  StackVector.cons ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ 0), (StackVector.cons
    ((Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), 0, StackVector.empty ())))

(** val operationCodes : Int64Word.t StackVector.t **)

let operationCodes =
  StackVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))), (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (StackVector.cons ((Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))))))))))))))))))), (Pervasives.succ
    (Pervasives.succ 0)), (StackVector.cons ((Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))))))))))))))))))),
    (Pervasives.succ 0), (StackVector.cons ((Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))))))),
    (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ 0)), (Int64Word.ws (false, (Pervasives.succ 0),
    (Int64Word.ws (false, 0, (Int64Word.w0))))))))))))))))))))))))))))))))),
    0, StackVector.empty ())))))))

(** val aRP_encoder_impl :
    OCamlNativeInt.t -> CstructBytestring.storage_t -> aRPPacket ->
    ((CstructBytestring.storage_t*OCamlNativeInt.t)*cacheFormat) option **)

let aRP_encoder_impl sz v r =
  match setCurrentBytes test_cache test_cache_add_nat sz (Pervasives.succ
          (Pervasives.succ 0)) v 0
          (StackVector.nth (Pervasives.succ (Pervasives.succ (Pervasives.succ
            0))) hardTypeCodes r.hardType) (Obj.magic ()) with
  | Some a ->
    (match setCurrentBytes test_cache test_cache_add_nat sz (Pervasives.succ
             (Pervasives.succ 0)) (let x,_ = let x,_ = a in x in x)
             (let _,y = let x,_ = a in x in y)
             (StackVector.nth (Pervasives.succ (Pervasives.succ 0))
               etherTypeCodes0 r.protType) (let _,y = a in y) with
     | Some a0 ->
       let idx = let _,y = let x,_ = a0 in x in y in
       if Nat.ltb idx sz
       then let a1 =
              ((CstructBytestring.set_nth sz
                 (let x,_ = let x,_ = a0 in x in x) idx
                 (StackVector.nth (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ 0))) hardSizeCodes r.hardType)),(Pervasives.succ
              idx)),(test_cache_add_nat.addE (let _,y = a0 in y)
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ 0)))))))))
            in
            let idx0 = let _,y = let x,_ = a1 in x in y in
            if Nat.ltb idx0 sz
            then let a2 =
                   ((CstructBytestring.set_nth sz
                      (let x,_ = let x,_ = a1 in x in x) idx0
                      (StackVector.nth (Pervasives.succ (Pervasives.succ 0))
                        protSizeCodes r.protType)),(Pervasives.succ
                   idx0)),(test_cache_add_nat.addE (let _,y = a1 in y)
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ 0)))))))))
                 in
                 (match setCurrentBytes test_cache test_cache_add_nat sz
                          (Pervasives.succ (Pervasives.succ 0))
                          (let x,_ = let x,_ = a2 in x in x)
                          (let _,y = let x,_ = a2 in x in y)
                          (StackVector.nth (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ (Pervasives.succ 0))))
                            operationCodes r.operation) (let _,y = a2 in y) with
                  | Some a3 ->
                    (match alignedEncodeList test_cache
                             (fun n0 v0 idx1 s ce ->
                             if Nat.ltb idx1 n0
                             then Some
                                    (((CstructBytestring.set_nth n0 v0 idx1 s),(Pervasives.succ
                                    idx1)),(test_cache_add_nat.addE ce
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0))))))))))
                             else None) sz (let x,_ = let x,_ = a3 in x in x)
                             (let _,y = let x,_ = a3 in x in y)
                             r.senderHardAddress (let _,y = a3 in y) with
                     | Some a4 ->
                       (match alignedEncodeList test_cache
                                (fun n0 v0 idx1 s ce ->
                                if Nat.ltb idx1 n0
                                then Some
                                       (((CstructBytestring.set_nth n0 v0
                                           idx1 s),(Pervasives.succ
                                       idx1)),(test_cache_add_nat.addE ce
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0))))))))))
                                else None) sz
                                (let x,_ = let x,_ = a4 in x in x)
                                (let _,y = let x,_ = a4 in x in y)
                                r.senderProtAddress (let _,y = a4 in y) with
                        | Some a5 ->
                          (match alignedEncodeList test_cache
                                   (fun n0 v0 idx1 s ce ->
                                   if Nat.ltb idx1 n0
                                   then Some
                                          (((CstructBytestring.set_nth n0 v0
                                              idx1 s),(Pervasives.succ
                                          idx1)),(test_cache_add_nat.addE ce
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ 0))))))))))
                                   else None) sz
                                   (let x,_ = let x,_ = a5 in x in x)
                                   (let _,y = let x,_ = a5 in x in y)
                                   r.targetHardAddress (let _,y = a5 in y) with
                           | Some a6 ->
                             alignedEncodeList test_cache
                               (fun n0 v0 idx1 s ce ->
                               if Nat.ltb idx1 n0
                               then Some
                                      (((CstructBytestring.set_nth n0 v0 idx1
                                          s),(Pervasives.succ
                                      idx1)),(test_cache_add_nat.addE ce
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0))))))))))
                               else None) sz
                               (let x,_ = let x,_ = a6 in x in x)
                               (let _,y = let x,_ = a6 in x in y)
                               r.targetProtAddress (let _,y = a6 in y)
                           | None -> None)
                        | None -> None)
                     | None -> None)
                  | None -> None)
            else None
       else None
     | None -> None)
  | None -> None

(** val aRP_decoder_impl :
    OCamlNativeInt.t -> CstructBytestring.storage_t ->
    ((aRPPacket*OCamlNativeInt.t)*cacheDecode) option **)

let aRP_decoder_impl sz v =
  match aligned_decode_enumN (Pervasives.succ (Pervasives.succ 0))
          (Pervasives.succ (Pervasives.succ 0)) test_cache test_cache_add_nat
          hardTypeCodes sz v 0 (Obj.magic ()) with
  | Some a ->
    let b = let x,_ = let x,_ = a in x in x in
    (match aligned_decode_enumN (Pervasives.succ (Pervasives.succ 0))
             (Pervasives.succ 0) test_cache test_cache_add_nat
             etherTypeCodes0 sz v (let _,y = let x,_ = a in x in y)
             (let _,y = a in y) with
     | Some a0 ->
       let b0 = let x,_ = let x,_ = a0 in x in x in
       let idx = let _,y = let x,_ = a0 in x in y in
       (match CstructBytestring.nth_opt sz v idx with
        | Some a1 ->
          let a2 = (a1,(Pervasives.succ
            idx)),(test_cache_add_nat.addD (let _,y = a0 in y)
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ 0)))))))))
          in
          let b1 = let x,_ = let x,_ = a2 in x in x in
          let idx0 = let _,y = let x,_ = a2 in x in y in
          (match CstructBytestring.nth_opt sz v idx0 with
           | Some a3 ->
             let a4 = (a3,(Pervasives.succ
               idx0)),(test_cache_add_nat.addD (let _,y = a2 in y)
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ 0)))))))))
             in
             let b2 = let x,_ = let x,_ = a4 in x in x in
             (match aligned_decode_enumN (Pervasives.succ (Pervasives.succ
                      0)) (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      0))) test_cache test_cache_add_nat operationCodes sz v
                      (let _,y = let x,_ = a4 in x in y) (let _,y = a4 in y) with
              | Some a5 ->
                (match listAlignedDecodeM test_cache sz
                         (fun numBytes v0 idx1 c ->
                         match CstructBytestring.nth_opt numBytes v0 idx1 with
                         | Some a6 ->
                           Some ((a6,(Pervasives.succ
                             idx1)),(test_cache_add_nat.addD c
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      0))))))))))
                         | None -> None)
                         (Int64Word.wordToNat (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ 0)))))))) b1) v
                         (let _,y = let x,_ = a5 in x in y)
                         (let _,y = a5 in y) with
                 | Some a6 ->
                   let l = let x,_ = let x,_ = a6 in x in x in
                   (match listAlignedDecodeM test_cache sz
                            (fun numBytes v0 idx1 c ->
                            match CstructBytestring.nth_opt numBytes v0 idx1 with
                            | Some a7 ->
                              Some ((a7,(Pervasives.succ
                                idx1)),(test_cache_add_nat.addD c
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         0))))))))))
                            | None -> None)
                            (Int64Word.wordToNat (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ 0)))))))) b2) v
                            (let _,y = let x,_ = a6 in x in y)
                            (let _,y = a6 in y) with
                    | Some a7 ->
                      let l0 = let x,_ = let x,_ = a7 in x in x in
                      (match listAlignedDecodeM test_cache sz
                               (fun numBytes v0 idx1 c ->
                               match CstructBytestring.nth_opt numBytes v0
                                       idx1 with
                               | Some a8 ->
                                 Some ((a8,(Pervasives.succ
                                   idx1)),(test_cache_add_nat.addD c
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            0))))))))))
                               | None -> None)
                               (Int64Word.wordToNat (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ 0)))))))) b1) v
                               (let _,y = let x,_ = a7 in x in y)
                               (let _,y = a7 in y) with
                       | Some a8 ->
                         let l1 = let x,_ = let x,_ = a8 in x in x in
                         (match listAlignedDecodeM test_cache sz
                                  (fun numBytes v0 idx1 c ->
                                  match CstructBytestring.nth_opt numBytes v0
                                          idx1 with
                                  | Some a9 ->
                                    Some ((a9,(Pervasives.succ
                                      idx1)),(test_cache_add_nat.addD c
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0))))))))))
                                  | None -> None)
                                  (Int64Word.wordToNat (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0)))))))) b2) v
                                  (let _,y = let x,_ = a8 in x in y)
                                  (let _,y = a8 in y) with
                          | Some a9 ->
                            let l2 = let x,_ = let x,_ = a9 in x in x in
                            let idx1 = let _,y = let x,_ = a9 in x in y in
                            let c = let _,y = a9 in y in
                            if (&&)
                                 ((&&)
                                   ((&&)
                                     ((=) (length l)
                                       (Int64Word.wordToNat (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ 0))))))))
                                         (StackVector.nth (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           0))) hardSizeCodes b)))
                                     ((&&)
                                       ((=) (length l0)
                                         (Int64Word.wordToNat
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           0))))))))
                                           (StackVector.nth (Pervasives.succ
                                             (Pervasives.succ 0))
                                             protSizeCodes b0)))
                                       ((&&)
                                         ((=) (length l1)
                                           (Int64Word.wordToNat
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0))))))))
                                             (StackVector.nth
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0)))
                                               hardSizeCodes b)))
                                         ((=) (length l2)
                                           (Int64Word.wordToNat
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0))))))))
                                             (StackVector.nth
                                               (Pervasives.succ
                                               (Pervasives.succ 0))
                                               protSizeCodes b0))))))
                                   (Int64Word.weqb (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ 0))))))))
                                     (StackVector.nth (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ 0)))
                                       hardSizeCodes b) b1))
                                 (Int64Word.weqb (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0))))))))
                                   (StackVector.nth (Pervasives.succ
                                     (Pervasives.succ 0)) protSizeCodes b0)
                                   b2)
                            then Some (({ hardType = b; protType = b0;
                                   operation =
                                   (let x,_ = let x,_ = a5 in x in x);
                                   senderHardAddress = l; senderProtAddress =
                                   l0; targetHardAddress = l1;
                                   targetProtAddress = l2 },idx1),c)
                            else None
                          | None -> None)
                       | None -> None)
                    | None -> None)
                 | None -> None)
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
  | None -> None

type iPv4_Packet = { totalLength : Int64Word.t; iD : Int64Word.t; dF : 
                     bool; mF : bool; fragmentOffset : Int64Word.t;
                     tTL : Int64Word.t; protocol : char list enumType;
                     sourceAddress : Int64Word.t; destAddress : Int64Word.t;
                     options : Int64Word.t list }

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

(** val protocolTypeCodes : Int64Word.t StackVector.t **)

let protocolTypeCodes =
  StackVector.cons ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ (Pervasives.succ 0)),
    (StackVector.cons ((Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))), (Int64Word.ws (true,
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))), (Int64Word.ws (false, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ 0)),
    (Int64Word.ws (false, (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), (Pervasives.succ 0), (StackVector.cons
    ((Int64Word.ws (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0))))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    0)))))), (Int64Word.ws (false, (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))), (Int64Word.ws
    (false, (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), (Int64Word.ws (true, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws (false,
    (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (false,
    (Pervasives.succ 0), (Int64Word.ws (false, 0,
    (Int64Word.w0))))))))))))))))), 0, StackVector.empty ())))))

(** val iPv4_Packet_Header_Len : iPv4_Packet -> OCamlNativeInt.t **)

let iPv4_Packet_Header_Len ip4 =
  add (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))) (length ip4.options)

(** val iPv4_encoder_impl :
    OCamlNativeInt.t -> CstructBytestring.storage_t -> iPv4_Packet ->
    ((CstructBytestring.storage_t*OCamlNativeInt.t)*cacheFormat) option **)

let iPv4_encoder_impl sz v r =
  match let idx = 0 in
        if Nat.ltb idx sz
        then let a =
               ((CstructBytestring.set_nth sz v idx
                  (Int64Word.combine (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ 0))))
                    (Int64Word.natToWord (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ 0))))
                      (iPv4_Packet_Header_Len r)) (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
                    (Int64Word.natToWord (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ (Pervasives.succ 0))))
                      (Pervasives.succ (Pervasives.succ (Pervasives.succ
                      (Pervasives.succ 0))))))),(Pervasives.succ
               idx)),(test_cache_add_nat.addE (Obj.magic ()) (Pervasives.succ
                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                       (Pervasives.succ (Pervasives.succ (Pervasives.succ
                       (Pervasives.succ 0)))))))))
             in
             let idx0 = let _,y = let x,_ = a in x in y in
             if Nat.ltb idx0 sz
             then let a0 =
                    ((CstructBytestring.set_nth sz
                       (let x,_ = let x,_ = a in x in x) idx0
                       (Int64Word.wzero (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         0)))))))))),(Pervasives.succ
                    idx0)),(test_cache_add_nat.addE (let _,y = a in y)
                             (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ 0)))))))))
                  in
                  let idx1 = let _,y = let x,_ = a0 in x in y in
                  (match let w = r.totalLength in
                         if Nat.ltb idx1 sz
                         then let a1 =
                                ((CstructBytestring.set_nth sz
                                   (let x,_ = let x,_ = a0 in x in x) idx1
                                   (Int64Word.split1' (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ 0))))))))
                                     (mul (Pervasives.succ 0)
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       0))))))))) w)),(Pervasives.succ
                                idx1)),(test_cache_add_nat.addE
                                         (let _,y = a0 in y) (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ 0)))))))))
                              in
                              let idx2 = let _,y = let x,_ = a1 in x in y in
                              let ce = let _,y = a1 in y in
                              if Nat.ltb idx2 sz
                              then Some
                                     (((CstructBytestring.set_nth sz
                                         (let x,_ = let x,_ = a1 in x in x)
                                         idx2
                                         (Int64Word.split2' (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ 0))))))))
                                           (mul (Pervasives.succ 0)
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                                     idx2)),(test_cache_add_nat.addE ce
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0))))))))))
                              else None
                         else None with
                   | Some a1 ->
                     let idx2 = let _,y = let x,_ = a1 in x in y in
                     (match let w = r.iD in
                            if Nat.ltb idx2 sz
                            then let a2 =
                                   ((CstructBytestring.set_nth sz
                                      (let x,_ = let x,_ = a1 in x in x) idx2
                                      (Int64Word.split1' (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ 0))))))))
                                        (mul (Pervasives.succ 0)
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0))))))))) w)),(Pervasives.succ
                                   idx2)),(test_cache_add_nat.addE
                                            (let _,y = a1 in y)
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            0)))))))))
                                 in
                                 let idx3 = let _,y = let x,_ = a2 in x in y
                                 in
                                 let ce = let _,y = a2 in y in
                                 if Nat.ltb idx3 sz
                                 then Some
                                        (((CstructBytestring.set_nth sz
                                            (let x,_ = let x,_ = a2 in x in x)
                                            idx3
                                            (Int64Word.split2'
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0))))))))
                                              (mul (Pervasives.succ 0)
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                                        idx3)),(test_cache_add_nat.addE ce
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ 0))))))))))
                                 else None
                            else None with
                      | Some a2 ->
                        let idx3 = let _,y = let x,_ = a2 in x in y in
                        (match let w =
                                 Int64Word.combine (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   0))))))))))))) r.fragmentOffset
                                   (add (Pervasives.succ 0)
                                     (add (Pervasives.succ 0)
                                       (Pervasives.succ 0)))
                                   (Int64Word.combine (Pervasives.succ 0)
                                     (Int64Word.ws (r.mF, 0, (Int64Word.w0)))
                                     (add (Pervasives.succ 0)
                                       (Pervasives.succ 0))
                                     (Int64Word.combine (Pervasives.succ 0)
                                       (Int64Word.ws (r.dF, 0,
                                       (Int64Word.w0))) (Pervasives.succ 0)
                                       (Int64Word.wzero (Pervasives.succ 0))))
                               in
                               if Nat.ltb idx3 sz
                               then let a3 =
                                      ((CstructBytestring.set_nth sz
                                         (let x,_ = let x,_ = a2 in x in x)
                                         idx3
                                         (Int64Word.split1' (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ 0))))))))
                                           (mul (Pervasives.succ 0)
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                                      idx3)),(test_cache_add_nat.addE
                                               (let _,y = a2 in y)
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0)))))))))
                                    in
                                    let idx4 =
                                      let _,y = let x,_ = a3 in x in y
                                    in
                                    let ce = let _,y = a3 in y in
                                    if Nat.ltb idx4 sz
                                    then Some
                                           (((CstructBytestring.set_nth sz
                                               (let x,_ = let x,_ = a3 in x in
                                                x) idx4
                                               (Int64Word.split2'
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ 0))))))))
                                                 (mul (Pervasives.succ 0)
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ 0)))))))))
                                                 w)),(Pervasives.succ
                                           idx4)),(test_cache_add_nat.addE ce
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0))))))))))
                                    else None
                               else None with
                         | Some a3 ->
                           let idx4 = let _,y = let x,_ = a3 in x in y in
                           if Nat.ltb idx4 sz
                           then let a4 =
                                  ((CstructBytestring.set_nth sz
                                     (let x,_ = let x,_ = a3 in x in x) idx4
                                     r.tTL),(Pervasives.succ
                                  idx4)),(test_cache_add_nat.addE
                                           (let _,y = a3 in y)
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           0)))))))))
                                in
                                let idx5 = let _,y = let x,_ = a4 in x in y in
                                if Nat.ltb idx5 sz
                                then Some
                                       (((CstructBytestring.set_nth sz
                                           (let x,_ = let x,_ = a4 in x in x)
                                           idx5
                                           (StackVector.nth (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0)))
                                             protocolTypeCodes r.protocol)),(Pervasives.succ
                                       idx5)),(test_cache_add_nat.addE
                                                (let _,y = a4 in y)
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0))))))))))
                                else None
                           else None
                         | None -> None)
                      | None -> None)
                   | None -> None)
             else None
        else None with
  | Some a ->
    let idx = let _,y = let x,_ = a in x in y in
    if Nat.ltb idx sz
    then let a0 =
           ((CstructBytestring.set_nth sz (let x,_ = let x,_ = a in x in x)
              idx
              (Int64Word.wzero (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))),(Pervasives.succ
           idx)),(test_cache_add_nat.addE (let _,y = a in y) (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ 0)))))))))
         in
         let idx0 = let _,y = let x,_ = a0 in x in y in
         if Nat.ltb idx0 sz
         then let a1 =
                ((CstructBytestring.set_nth sz
                   (let x,_ = let x,_ = a0 in x in x) idx0
                   (Int64Word.wzero (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     0)))))))))),(Pervasives.succ
                idx0)),(test_cache_add_nat.addE (let _,y = a0 in y)
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ 0)))))))))
              in
              let idx1 = let _,y = let x,_ = a1 in x in y in
              (match match let w = r.sourceAddress in
                           if Nat.ltb idx1 sz
                           then let a2 =
                                  ((CstructBytestring.set_nth sz
                                     (let x,_ = let x,_ = a1 in x in x) idx1
                                     (Int64Word.split1' (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ 0))))))))
                                       (mul (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ 0)))
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         0))))))))) w)),(Pervasives.succ
                                  idx1)),(test_cache_add_nat.addE
                                           (let _,y = a1 in y)
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           0)))))))))
                                in
                                let idx2 = let _,y = let x,_ = a2 in x in y in
                                let s =
                                  Int64Word.split2' (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0))))))))
                                    (mul (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ 0))) (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ 0))))))))) w
                                in
                                let c = let _,y = a2 in y in
                                if Nat.ltb idx2 sz
                                then let a3 =
                                       ((CstructBytestring.set_nth sz
                                          (let x,_ = let x,_ = a2 in x in x)
                                          idx2
                                          (Int64Word.split1' (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ 0))))))))
                                            (mul (Pervasives.succ
                                              (Pervasives.succ 0))
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0))))))))) s)),(Pervasives.succ
                                       idx2)),(test_cache_add_nat.addE c
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0)))))))))
                                     in
                                     let idx3 =
                                       let _,y = let x,_ = a3 in x in y
                                     in
                                     let s0 =
                                       Int64Word.split2' (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ 0))))))))
                                         (mul (Pervasives.succ
                                           (Pervasives.succ 0))
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           0))))))))) s
                                     in
                                     let c0 = let _,y = a3 in y in
                                     if Nat.ltb idx3 sz
                                     then let a4 =
                                            ((CstructBytestring.set_nth sz
                                               (let x,_ = let x,_ = a3 in x in
                                                x) idx3
                                               (Int64Word.split1'
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ 0))))))))
                                                 (mul (Pervasives.succ 0)
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ 0)))))))))
                                                 s0)),(Pervasives.succ
                                            idx3)),(test_cache_add_nat.addE
                                                     c0 (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     0)))))))))
                                          in
                                          let idx4 =
                                            let _,y = let x,_ = a4 in x in y
                                          in
                                          let ce = let _,y = a4 in y in
                                          if Nat.ltb idx4 sz
                                          then Some
                                                 (((CstructBytestring.set_nth
                                                     sz
                                                     (let x,_ =
                                                        let x,_ = a4 in x
                                                      in
                                                      x) idx4
                                                     (Int64Word.split2'
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       0))))))))
                                                       (mul (Pervasives.succ
                                                         0) (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         0))))))))) s0)),(Pervasives.succ
                                                 idx4)),(test_cache_add_nat.addE
                                                          ce (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          0))))))))))
                                          else None
                                     else None
                                else None
                           else None with
                     | Some a2 ->
                       let idx2 = let _,y = let x,_ = a2 in x in y in
                       (match let w = r.destAddress in
                              if Nat.ltb idx2 sz
                              then let a3 =
                                     ((CstructBytestring.set_nth sz
                                        (let x,_ = let x,_ = a2 in x in x)
                                        idx2
                                        (Int64Word.split1' (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ 0))))))))
                                          (mul (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            0))) (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                                     idx2)),(test_cache_add_nat.addE
                                              (let _,y = a2 in y)
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0)))))))))
                                   in
                                   let idx3 = let _,y = let x,_ = a3 in x in y
                                   in
                                   let s =
                                     Int64Word.split2' (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ 0))))))))
                                       (mul (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ 0)))
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         0))))))))) w
                                   in
                                   let c = let _,y = a3 in y in
                                   if Nat.ltb idx3 sz
                                   then let a4 =
                                          ((CstructBytestring.set_nth sz
                                             (let x,_ = let x,_ = a3 in x in x)
                                             idx3
                                             (Int64Word.split1'
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0))))))))
                                               (mul (Pervasives.succ
                                                 (Pervasives.succ 0))
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ 0)))))))))
                                               s)),(Pervasives.succ
                                          idx3)),(test_cache_add_nat.addE c
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ 0)))))))))
                                        in
                                        let idx4 =
                                          let _,y = let x,_ = a4 in x in y
                                        in
                                        let s0 =
                                          Int64Word.split2' (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ 0))))))))
                                            (mul (Pervasives.succ
                                              (Pervasives.succ 0))
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0))))))))) s
                                        in
                                        let c0 = let _,y = a4 in y in
                                        if Nat.ltb idx4 sz
                                        then let a5 =
                                               ((CstructBytestring.set_nth sz
                                                  (let x,_ = let x,_ = a4 in x
                                                   in
                                                   x) idx4
                                                  (Int64Word.split1'
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0))))))))
                                                    (mul (Pervasives.succ 0)
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      0))))))))) s0)),(Pervasives.succ
                                               idx4)),(test_cache_add_nat.addE
                                                        c0 (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        0)))))))))
                                             in
                                             let idx5 =
                                               let _,y = let x,_ = a5 in x in
                                               y
                                             in
                                             let ce = let _,y = a5 in y in
                                             if Nat.ltb idx5 sz
                                             then Some
                                                    (((CstructBytestring.set_nth
                                                        sz
                                                        (let x,_ =
                                                           let x,_ = a5 in x
                                                         in
                                                         x) idx5
                                                        (Int64Word.split2'
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          0))))))))
                                                          (mul
                                                            (Pervasives.succ
                                                            0)
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0))))))))) s0)),(Pervasives.succ
                                                    idx5)),(test_cache_add_nat.addE
                                                             ce
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             0))))))))))
                                             else None
                                        else None
                                   else None
                              else None with
                        | Some a3 ->
                          alignedEncodeList test_cache (fun n0 v0 idx3 w c ->
                            if Nat.ltb idx3 n0
                            then let a4 =
                                   ((CstructBytestring.set_nth n0 v0 idx3
                                      (Int64Word.split1' (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ 0))))))))
                                        (mul (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0))) (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                                   idx3)),(test_cache_add_nat.addE c
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            0)))))))))
                                 in
                                 let idx4 = let _,y = let x,_ = a4 in x in y
                                 in
                                 let s =
                                   Int64Word.split2' (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ 0))))))))
                                     (mul (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ 0))) (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ 0))))))))) w
                                 in
                                 let c0 = let _,y = a4 in y in
                                 if Nat.ltb idx4 n0
                                 then let a5 =
                                        ((CstructBytestring.set_nth n0
                                           (let x,_ = let x,_ = a4 in x in x)
                                           idx4
                                           (Int64Word.split1'
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0))))))))
                                             (mul (Pervasives.succ
                                               (Pervasives.succ 0))
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0))))))))) s)),(Pervasives.succ
                                        idx4)),(test_cache_add_nat.addE c0
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ 0)))))))))
                                      in
                                      let idx5 =
                                        let _,y = let x,_ = a5 in x in y
                                      in
                                      let s0 =
                                        Int64Word.split2' (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ 0))))))))
                                          (mul (Pervasives.succ
                                            (Pervasives.succ 0))
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            0))))))))) s
                                      in
                                      let c1 = let _,y = a5 in y in
                                      if Nat.ltb idx5 n0
                                      then let a6 =
                                             ((CstructBytestring.set_nth n0
                                                (let x,_ = let x,_ = a5 in x
                                                 in
                                                 x) idx5
                                                (Int64Word.split1'
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0))))))))
                                                  (mul (Pervasives.succ 0)
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0))))))))) s0)),(Pervasives.succ
                                             idx5)),(test_cache_add_nat.addE
                                                      c1 (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      0)))))))))
                                           in
                                           let idx6 =
                                             let _,y = let x,_ = a6 in x in y
                                           in
                                           let ce = let _,y = a6 in y in
                                           if Nat.ltb idx6 n0
                                           then Some
                                                  (((CstructBytestring.set_nth
                                                      n0
                                                      (let x,_ =
                                                         let x,_ = a6 in x
                                                       in
                                                       x) idx6
                                                      (Int64Word.split2'
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        0))))))))
                                                        (mul (Pervasives.succ
                                                          0) (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          0))))))))) s0)),(Pervasives.succ
                                                  idx6)),(test_cache_add_nat.addE
                                                           ce
                                                           (Pervasives.succ
                                                           (Pervasives.succ
                                                           (Pervasives.succ
                                                           (Pervasives.succ
                                                           (Pervasives.succ
                                                           (Pervasives.succ
                                                           (Pervasives.succ
                                                           (Pervasives.succ
                                                           0))))))))))
                                           else None
                                      else None
                                 else None
                            else None) sz (let x,_ = let x,_ = a3 in x in x)
                            (let _,y = let x,_ = a3 in x in y) r.options
                            (let _,y = a3 in y)
                        | None -> None)
                     | None -> None with
               | Some a2 ->
                 calculate_IPChecksum sz (let x,_ = let x,_ = a2 in x in x)
                   (let _,y = let x,_ = a2 in x in y) r (let _,y = a2 in y)
               | None -> None)
         else None
    else None
  | None -> None

(** val iPv4_decoder_impl :
    OCamlNativeInt.t -> CstructBytestring.storage_t ->
    ((iPv4_Packet*OCamlNativeInt.t)*unit) option **)

let iPv4_decoder_impl sz v =
  if Int64Word.weq (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))))
       (CstructBytestring.checksum_bound (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
         (Pervasives.succ (Pervasives.succ 0)))))))))))))))))))) sz v)
       (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0)))))))))))))), (Int64Word.ws
       (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0)))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))), (Int64Word.ws (true, (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0)))))))))), (Int64Word.ws (true, (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0)))))))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
       (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0)))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
       (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
       (true, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (true,
       (Pervasives.succ 0), (Int64Word.ws (true, 0,
       (Int64Word.w0)))))))))))))))))))))))))))))))))
  then let idx = Obj.magic 0 in
       let c = Obj.magic () in
       (match CstructBytestring.nth_opt sz v idx with
        | Some a ->
          let a0 = (a,(Pervasives.succ
            idx)),(test_cache_add_nat.addD c (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ 0)))))))))
          in
          let b = let x,_ = let x,_ = a0 in x in x in
          (match skipCurrentByte test_cache test_cache_add_nat sz v
                   (let _,y = let x,_ = a0 in x in y) (let _,y = a0 in y) with
           | Some a1 ->
             let idx0 = let _,y = let x,_ = a1 in x in y in
             (match CstructBytestring.nth_opt sz v idx0 with
              | Some a2 ->
                let a3 = (a2,(Pervasives.succ
                  idx0)),(test_cache_add_nat.addD (let _,y = a1 in y)
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ 0)))))))))
                in
                let idx1 = let _,y = let x,_ = a3 in x in y in
                (match CstructBytestring.nth_opt sz v idx1 with
                 | Some a4 ->
                   let a5 = (a4,(Pervasives.succ
                     idx1)),(test_cache_add_nat.addD (let _,y = a3 in y)
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ 0)))))))))
                   in
                   let a6 =
                     ((Int64Word.append (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        0)))))))) (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        0)))))))) (let x,_ = let x,_ = a5 in x in x)
                        (let x,_ = let x,_ = a3 in x in x)),(let _,y =
                                                               let x,_ = a5 in
                                                               x
                                                             in
                                                             y)),(let _,y = a5
                                                                  in
                                                                  y)
                   in
                   let w = let x,_ = let x,_ = a6 in x in x in
                   let idx2 = let _,y = let x,_ = a6 in x in y in
                   (match CstructBytestring.nth_opt sz v idx2 with
                    | Some a7 ->
                      let a8 = (a7,(Pervasives.succ
                        idx2)),(test_cache_add_nat.addD (let _,y = a6 in y)
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ 0)))))))))
                      in
                      let idx3 = let _,y = let x,_ = a8 in x in y in
                      (match CstructBytestring.nth_opt sz v idx3 with
                       | Some a9 ->
                         let a10 = (a9,(Pervasives.succ
                           idx3)),(test_cache_add_nat.addD
                                    (let _,y = a8 in y) (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0)))))))))
                         in
                         let a11 =
                           ((Int64Word.append (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ 0)))))))) (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ 0))))))))
                              (let x,_ = let x,_ = a10 in x in x)
                              (let x,_ = let x,_ = a8 in x in x)),(let _,y =
                                                                    let x,_ =
                                                                    a10
                                                                    in
                                                                    x
                                                                   in
                                                                   y)),
                           (let _,y = a10 in y)
                         in
                         let idx4 = let _,y = let x,_ = a11 in x in y in
                         (match CstructBytestring.nth_opt sz v idx4 with
                          | Some a12 ->
                            let a13 = (a12,(Pervasives.succ
                              idx4)),(test_cache_add_nat.addD
                                       (let _,y = a11 in y) (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ 0)))))))))
                            in
                            let idx5 = let _,y = let x,_ = a13 in x in y in
                            (match CstructBytestring.nth_opt sz v idx5 with
                             | Some a14 ->
                               let a15 = (a14,(Pervasives.succ
                                 idx5)),(test_cache_add_nat.addD
                                          (let _,y = a13 in y)
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0)))))))))
                               in
                               let a16 =
                                 ((Int64Word.append (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0))))))))
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    0))))))))
                                    (let x,_ = let x,_ = a15 in x in x)
                                    (let x,_ = let x,_ = a13 in x in x)),
                                 (let _,y = let x,_ = a15 in x in y)),
                                 (let _,y = a15 in y)
                               in
                               let w0 = let x,_ = let x,_ = a16 in x in x in
                               let idx6 = let _,y = let x,_ = a16 in x in y in
                               (match CstructBytestring.nth_opt sz v idx6 with
                                | Some a17 ->
                                  let a18 = (a17,(Pervasives.succ
                                    idx6)),(test_cache_add_nat.addD
                                             (let _,y = a16 in y)
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0)))))))))
                                  in
                                  (match aligned_decode_enum (Pervasives.succ
                                           (Pervasives.succ 0)) test_cache
                                           test_cache_add_nat
                                           protocolTypeCodes sz v
                                           (let _,y = let x,_ = a18 in x in y)
                                           (let _,y = a18 in y) with
                                   | Some a19 ->
                                     (match skipCurrentByte test_cache
                                              test_cache_add_nat sz v
                                              (let _,y = let x,_ = a19 in x in
                                               y) (let _,y = a19 in y) with
                                      | Some a20 ->
                                        (match skipCurrentByte test_cache
                                                 test_cache_add_nat sz v
                                                 (let _,y = let x,_ = a20 in x
                                                  in
                                                  y) (let _,y = a20 in y) with
                                         | Some a21 ->
                                           let idx7 =
                                             let _,y = let x,_ = a21 in x in y
                                           in
                                           (match CstructBytestring.nth_opt
                                                    sz v idx7 with
                                            | Some a22 ->
                                              let a23 = (a22,(Pervasives.succ
                                                idx7)),(test_cache_add_nat.addD
                                                         (let _,y = a21 in y)
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         (Pervasives.succ
                                                         0)))))))))
                                              in
                                              let idx8 =
                                                let _,y = let x,_ = a23 in x
                                                in
                                                y
                                              in
                                              (match CstructBytestring.nth_opt
                                                       sz v idx8 with
                                               | Some a24 ->
                                                 let a25 =
                                                   (a24,(Pervasives.succ
                                                   idx8)),(test_cache_add_nat.addD
                                                            (let _,y = a23 in
                                                             y)
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0)))))))))
                                                 in
                                                 let idx9 =
                                                   let _,y =
                                                     let x,_ = a25 in x
                                                   in
                                                   y
                                                 in
                                                 (match CstructBytestring.nth_opt
                                                          sz v idx9 with
                                                  | Some a26 ->
                                                    let a27 =
                                                      (a26,(Pervasives.succ
                                                      idx9)),(test_cache_add_nat.addD
                                                               (let _,y = a25
                                                                in
                                                                y)
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               0)))))))))
                                                    in
                                                    let idx10 =
                                                      let _,y =
                                                        let x,_ = a27 in x
                                                      in
                                                      y
                                                    in
                                                    (match CstructBytestring.nth_opt
                                                             sz v idx10 with
                                                     | Some a28 ->
                                                       let a29 =
                                                         (a28,(Pervasives.succ
                                                         idx10)),(test_cache_add_nat.addD
                                                                   (let _,y =
                                                                    a27
                                                                    in
                                                                    y)
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   0)))))))))
                                                       in
                                                       let a30 =
                                                         ((Int64Word.append
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0))))))))
                                                            (add
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              0))))))))
                                                              (add
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0))))))))
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0))))))))))
                                                            (let x,_ =
                                                               let x,_ = a29
                                                               in
                                                               x
                                                             in
                                                             x)
                                                            (Int64Word.append
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              0))))))))
                                                              (add
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0))))))))
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0)))))))))
                                                              (let x,_ =
                                                                 let x,_ = a27
                                                                 in
                                                                 x
                                                               in
                                                               x)
                                                              (Int64Word.append
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0))))))))
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0))))))))
                                                                (let x,_ =
                                                                   let x,_ =
                                                                    a25
                                                                   in
                                                                   x
                                                                 in
                                                                 x)
                                                                (let x,_ =
                                                                   let x,_ =
                                                                    a23
                                                                   in
                                                                   x
                                                                 in
                                                                 x)))),
                                                         (let _,y =
                                                            let x,_ = a29 in x
                                                          in
                                                          y)),(let _,y = a29
                                                               in
                                                               y)
                                                       in
                                                       let idx11 =
                                                         let _,y =
                                                           let x,_ = a30 in x
                                                         in
                                                         y
                                                       in
                                                       (match CstructBytestring.nth_opt
                                                                sz v idx11 with
                                                        | Some a31 ->
                                                          let a32 =
                                                            (a31,(Pervasives.succ
                                                            idx11)),(test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a30
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                          in
                                                          let idx12 =
                                                            let _,y =
                                                              let x,_ = a32 in
                                                              x
                                                            in
                                                            y
                                                          in
                                                          (match CstructBytestring.nth_opt
                                                                   sz v idx12 with
                                                           | Some a33 ->
                                                             let a34 =
                                                               (a33,(Pervasives.succ
                                                               idx12)),
                                                               (test_cache_add_nat.addD
                                                                 (let _,y =
                                                                    a32
                                                                  in
                                                                  y)
                                                                 (Pervasives.succ
                                                                 (Pervasives.succ
                                                                 (Pervasives.succ
                                                                 (Pervasives.succ
                                                                 (Pervasives.succ
                                                                 (Pervasives.succ
                                                                 (Pervasives.succ
                                                                 (Pervasives.succ
                                                                 0)))))))))
                                                             in
                                                             let idx13 =
                                                               let _,y =
                                                                 let x,_ = a34
                                                                 in
                                                                 x
                                                               in
                                                               y
                                                             in
                                                             (match CstructBytestring.nth_opt
                                                                    sz v idx13 with
                                                              | Some a35 ->
                                                                let a36 =
                                                                  (a35,(Pervasives.succ
                                                                  idx13)),
                                                                  (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a34
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                in
                                                                let idx14 =
                                                                  let _,y =
                                                                    let x,_ =
                                                                    a36
                                                                    in
                                                                    x
                                                                  in
                                                                  y
                                                                in
                                                                (match 
                                                                 CstructBytestring.nth_opt
                                                                   sz v idx14 with
                                                                 | Some a37 ->
                                                                   let a38 =
                                                                    (a37,(Pervasives.succ
                                                                    idx14)),
                                                                    (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a36
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                   in
                                                                   let a39 =
                                                                    ((Int64Word.append
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (add
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (add
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a38
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (Int64Word.append
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (add
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a36
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (Int64Word.append
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a34
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a32
                                                                    in
                                                                    x
                                                                    in
                                                                    x)))),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a38
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a38
                                                                    in
                                                                    y)
                                                                   in
                                                                   (match 
                                                                    listAlignedDecodeM
                                                                    test_cache
                                                                    sz
                                                                    (fun numBytes v0 idx15 c0 ->
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    numBytes
                                                                    v0 idx15 with
                                                                    | Some a40 ->
                                                                    let a41 =
                                                                    (a40,(Pervasives.succ
                                                                    idx15)),
                                                                    (test_cache_add_nat.addD
                                                                    c0
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let idx16 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a41
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    (
                                                                    match 
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    numBytes
                                                                    v0 idx16 with
                                                                    | Some a42 ->
                                                                    let a43 =
                                                                    (a42,(Pervasives.succ
                                                                    idx16)),
                                                                    (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a41
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let idx17 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a43
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    (
                                                                    match 
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    numBytes
                                                                    v0 idx17 with
                                                                    | Some a44 ->
                                                                    let a45 =
                                                                    (a44,(Pervasives.succ
                                                                    idx17)),
                                                                    (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a43
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let idx18 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a45
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    (
                                                                    match 
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    numBytes
                                                                    v0 idx18 with
                                                                    | Some a46 ->
                                                                    let a47 =
                                                                    (a46,(Pervasives.succ
                                                                    idx18)),
                                                                    (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a45
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let a48 =
                                                                    ((Int64Word.w0),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a47
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a47
                                                                    in
                                                                    y)
                                                                    in
                                                                    Some
                                                                    ((
                                                                    (Int64Word.append
                                                                    (mul 0
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a48
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a47
                                                                    in
                                                                    x
                                                                    in
                                                                    x)),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a48
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a48
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None with
                                                                    | Some a46 ->
                                                                    Some
                                                                    (((Int64Word.append
                                                                    (mul
                                                                    (Pervasives.succ
                                                                    0)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a46
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a45
                                                                    in
                                                                    x
                                                                    in
                                                                    x)),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a46
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a46
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None)
                                                                    | None ->
                                                                    None with
                                                                    | Some a44 ->
                                                                    Some
                                                                    (((Int64Word.append
                                                                    (mul
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a44
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a43
                                                                    in
                                                                    x
                                                                    in
                                                                    x)),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a44
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a44
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None)
                                                                    | None ->
                                                                    None with
                                                                    | Some a42 ->
                                                                    Some
                                                                    (((Int64Word.append
                                                                    (mul
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a42
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a41
                                                                    in
                                                                    x
                                                                    in
                                                                    x)),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a42
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a42
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None)
                                                                    | None ->
                                                                    None)
                                                                    (sub
                                                                    (Int64Word.wordToNat
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (id
                                                                    (Int64Word.split2'
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))) b)))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))) v
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a39
                                                                    in
                                                                    x
                                                                    in
                                                                    y)
                                                                    (
                                                                    let _,y =
                                                                    a39
                                                                    in
                                                                    y) with
                                                                    | Some a40 ->
                                                                    let l =
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a40
                                                                    in
                                                                    x
                                                                    in
                                                                    x
                                                                    in
                                                                    let idx15 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a40
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    let c0 =
                                                                    let _,y =
                                                                    a40
                                                                    in
                                                                    y
                                                                    in
                                                                    if 
                                                                    (&&)
                                                                    ((&&)
                                                                    ((&&)
                                                                    (if 
                                                                    (<)
                                                                    (length l)
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
                                                                    then true
                                                                    else false)
                                                                    (if 
                                                                    (<)
                                                                    (add
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
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))))))))))))))
                                                                    (mul
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (length l)))
                                                                    (Int64Word.wordToNat
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
                                                                    (Pervasives.succ
                                                                    0))))))))))))))))
                                                                    w)
                                                                    then true
                                                                    else false))
                                                                    (if 
                                                                    Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b))))
                                                                    then false
                                                                    else 
                                                                    if 
                                                                    Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b)))))
                                                                    then false
                                                                    else 
                                                                    if 
                                                                    Int64Word.whd
                                                                    (Pervasives.succ
                                                                    0)
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b))))))
                                                                    then 
                                                                    if 
                                                                    Int64Word.whd
                                                                    0
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    0)
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b)))))))
                                                                    then false
                                                                    else true
                                                                    else false))
                                                                    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun m' ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun m'0 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun m'1 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun m'2 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun m'3 ->
                                                                    (=)
                                                                    (length l)
                                                                    m'3)
                                                                    m'2)
                                                                    m'1)
                                                                    m'0)
                                                                    m')
                                                                    (Int64Word.wordToNat
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (id
                                                                    (Int64Word.split2'
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))) b))))
                                                                    then 
                                                                    Obj.magic
                                                                    (Some
                                                                    (({ totalLength =
                                                                    w; iD =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a11
                                                                    in
                                                                    x
                                                                    in
                                                                    x); dF =
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    0)
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
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
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
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
                                                                    w0))))))))))))));
                                                                    fragmentOffset =
                                                                    (id
                                                                    (Int64Word.split2'
                                                                    (add
                                                                    (add
                                                                    (Pervasives.succ
                                                                    0)
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Pervasives.succ
                                                                    0))
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
                                                                    w0));
                                                                    tTL =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a18
                                                                    in
                                                                    x
                                                                    in
                                                                    x);
                                                                    protocol =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a19
                                                                    in
                                                                    x
                                                                    in
                                                                    x);
                                                                    sourceAddress =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a30
                                                                    in
                                                                    x
                                                                    in
                                                                    x);
                                                                    destAddress =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a39
                                                                    in
                                                                    x
                                                                    in
                                                                    x);
                                                                    options =
                                                                    l },idx15),c0))
                                                                    else 
                                                                    Obj.magic
                                                                    None
                                                                    | None ->
                                                                    Obj.magic
                                                                    None)
                                                                 | None ->
                                                                   Obj.magic
                                                                    None)
                                                              | None ->
                                                                Obj.magic None)
                                                           | None ->
                                                             Obj.magic None)
                                                        | None ->
                                                          Obj.magic None)
                                                     | None -> Obj.magic None)
                                                  | None -> Obj.magic None)
                                               | None -> Obj.magic None)
                                            | None -> Obj.magic None)
                                         | None -> Obj.magic None)
                                      | None -> Obj.magic None)
                                   | None -> Obj.magic None)
                                | None -> Obj.magic None)
                             | None -> Obj.magic None)
                          | None -> Obj.magic None)
                       | None -> Obj.magic None)
                    | None -> Obj.magic None)
                 | None -> Obj.magic None)
              | None -> Obj.magic None)
           | None -> Obj.magic None)
        | None -> Obj.magic None)
  else Obj.magic None

type tCP_Packet = { sourcePort : Int64Word.t; destPort : Int64Word.t;
                    seqNumber : Int64Word.t; ackNumber : Int64Word.t;
                    nS : bool; cWR : bool; eCE : bool; aCK : bool;
                    pSH : bool; rST : bool; sYN : bool; fIN : bool;
                    windowSize : Int64Word.t;
                    urgentPointer : Int64Word.t option;
                    options0 : Int64Word.t list;
                    payload : (OCamlNativeInt.t, CstructBytestring.storage_t)
                              sigT }

(** val sourcePort : tCP_Packet -> Int64Word.t **)

let sourcePort x = x.sourcePort

(** val destPort : tCP_Packet -> Int64Word.t **)

let destPort x = x.destPort

(** val seqNumber : tCP_Packet -> Int64Word.t **)

let seqNumber x = x.seqNumber

(** val ackNumber : tCP_Packet -> Int64Word.t **)

let ackNumber x = x.ackNumber

(** val nS : tCP_Packet -> bool **)

let nS x = x.nS

(** val cWR : tCP_Packet -> bool **)

let cWR x = x.cWR

(** val eCE : tCP_Packet -> bool **)

let eCE x = x.eCE

(** val aCK : tCP_Packet -> bool **)

let aCK x = x.aCK

(** val pSH : tCP_Packet -> bool **)

let pSH x = x.pSH

(** val rST : tCP_Packet -> bool **)

let rST x = x.rST

(** val sYN : tCP_Packet -> bool **)

let sYN x = x.sYN

(** val fIN : tCP_Packet -> bool **)

let fIN x = x.fIN

(** val windowSize : tCP_Packet -> Int64Word.t **)

let windowSize x = x.windowSize

(** val urgentPointer : tCP_Packet -> Int64Word.t option **)

let urgentPointer x = x.urgentPointer

(** val options0 : tCP_Packet -> Int64Word.t list **)

let options0 x = x.options0

(** val payload :
    tCP_Packet -> (OCamlNativeInt.t, CstructBytestring.storage_t) sigT **)

let payload x = x.payload

(** val tCP_encoder_impl :
    CstructBytestring.storage_t -> CstructBytestring.storage_t -> Int64Word.t
    -> tCP_Packet -> OCamlNativeInt.t -> CstructBytestring.storage_t ->
    ((CstructBytestring.storage_t*OCamlNativeInt.t)*cacheFormat) option **)

let tCP_encoder_impl srcAddr destAddr tcpLength r sz v =
  match let idx = 0 in
        (match let w = r.sourcePort in
               if Nat.ltb idx sz
               then let a =
                      ((CstructBytestring.set_nth sz v idx
                         (Int64Word.split1' (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           0))))))))
                           (mul (Pervasives.succ 0) (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                      idx)),(test_cache_add_nat.addE (Obj.magic ())
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ 0)))))))))
                    in
                    let idx0 = let _,y = let x,_ = a in x in y in
                    let ce = let _,y = a in y in
                    if Nat.ltb idx0 sz
                    then Some
                           (((CstructBytestring.set_nth sz
                               (let x,_ = let x,_ = a in x in x) idx0
                               (Int64Word.split2' (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ 0))))))))
                                 (mul (Pervasives.succ 0) (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                           idx0)),(test_cache_add_nat.addE ce
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    0))))))))))
                    else None
               else None with
         | Some a ->
           let idx0 = let _,y = let x,_ = a in x in y in
           (match let w = r.destPort in
                  if Nat.ltb idx0 sz
                  then let a0 =
                         ((CstructBytestring.set_nth sz
                            (let x,_ = let x,_ = a in x in x) idx0
                            (Int64Word.split1' (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ 0))))))))
                              (mul (Pervasives.succ 0) (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                         idx0)),(test_cache_add_nat.addE (let _,y = a in y)
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ 0)))))))))
                       in
                       let idx1 = let _,y = let x,_ = a0 in x in y in
                       let ce = let _,y = a0 in y in
                       if Nat.ltb idx1 sz
                       then Some
                              (((CstructBytestring.set_nth sz
                                  (let x,_ = let x,_ = a0 in x in x) idx1
                                  (Int64Word.split2' (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0))))))))
                                    (mul (Pervasives.succ 0) (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                              idx1)),(test_cache_add_nat.addE ce
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       0))))))))))
                       else None
                  else None with
            | Some a0 ->
              let idx1 = let _,y = let x,_ = a0 in x in y in
              (match let w = r.seqNumber in
                     if Nat.ltb idx1 sz
                     then let a1 =
                            ((CstructBytestring.set_nth sz
                               (let x,_ = let x,_ = a0 in x in x) idx1
                               (Int64Word.split1' (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ 0))))))))
                                 (mul (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0))) (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                            idx1)),(test_cache_add_nat.addE
                                     (let _,y = a0 in y) (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ 0)))))))))
                          in
                          let idx2 = let _,y = let x,_ = a1 in x in y in
                          let s =
                            Int64Word.split2' (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ 0))))))))
                              (mul (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ 0))) (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ 0))))))))) w
                          in
                          let c = let _,y = a1 in y in
                          if Nat.ltb idx2 sz
                          then let a2 =
                                 ((CstructBytestring.set_nth sz
                                    (let x,_ = let x,_ = a1 in x in x) idx2
                                    (Int64Word.split1' (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ 0))))))))
                                      (mul (Pervasives.succ (Pervasives.succ
                                        0)) (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        0))))))))) s)),(Pervasives.succ
                                 idx2)),(test_cache_add_nat.addE c
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0)))))))))
                               in
                               let idx3 = let _,y = let x,_ = a2 in x in y in
                               let s0 =
                                 Int64Word.split2' (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0))))))))
                                   (mul (Pervasives.succ (Pervasives.succ 0))
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     (Pervasives.succ (Pervasives.succ
                                     0))))))))) s
                               in
                               let c0 = let _,y = a2 in y in
                               if Nat.ltb idx3 sz
                               then let a3 =
                                      ((CstructBytestring.set_nth sz
                                         (let x,_ = let x,_ = a2 in x in x)
                                         idx3
                                         (Int64Word.split1' (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ 0))))))))
                                           (mul (Pervasives.succ 0)
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0))))))))) s0)),(Pervasives.succ
                                      idx3)),(test_cache_add_nat.addE c0
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0)))))))))
                                    in
                                    let idx4 =
                                      let _,y = let x,_ = a3 in x in y
                                    in
                                    let ce = let _,y = a3 in y in
                                    if Nat.ltb idx4 sz
                                    then Some
                                           (((CstructBytestring.set_nth sz
                                               (let x,_ = let x,_ = a3 in x in
                                                x) idx4
                                               (Int64Word.split2'
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ 0))))))))
                                                 (mul (Pervasives.succ 0)
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ 0)))))))))
                                                 s0)),(Pervasives.succ
                                           idx4)),(test_cache_add_nat.addE ce
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0))))))))))
                                    else None
                               else None
                          else None
                     else None with
               | Some a1 ->
                 let idx2 = let _,y = let x,_ = a1 in x in y in
                 (match let w = r.ackNumber in
                        if Nat.ltb idx2 sz
                        then let a2 =
                               ((CstructBytestring.set_nth sz
                                  (let x,_ = let x,_ = a1 in x in x) idx2
                                  (Int64Word.split1' (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0))))))))
                                    (mul (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ 0))) (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                               idx2)),(test_cache_add_nat.addE
                                        (let _,y = a1 in y) (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ 0)))))))))
                             in
                             let idx3 = let _,y = let x,_ = a2 in x in y in
                             let s =
                               Int64Word.split2' (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ 0))))))))
                                 (mul (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0))) (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0))))))))) w
                             in
                             let c = let _,y = a2 in y in
                             if Nat.ltb idx3 sz
                             then let a3 =
                                    ((CstructBytestring.set_nth sz
                                       (let x,_ = let x,_ = a2 in x in x)
                                       idx3
                                       (Int64Word.split1' (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ 0))))))))
                                         (mul (Pervasives.succ
                                           (Pervasives.succ 0))
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           0))))))))) s)),(Pervasives.succ
                                    idx3)),(test_cache_add_nat.addE c
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0)))))))))
                                  in
                                  let idx4 = let _,y = let x,_ = a3 in x in y
                                  in
                                  let s0 =
                                    Int64Word.split2' (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ 0))))))))
                                      (mul (Pervasives.succ (Pervasives.succ
                                        0)) (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        0))))))))) s
                                  in
                                  let c0 = let _,y = a3 in y in
                                  if Nat.ltb idx4 sz
                                  then let a4 =
                                         ((CstructBytestring.set_nth sz
                                            (let x,_ = let x,_ = a3 in x in x)
                                            idx4
                                            (Int64Word.split1'
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0))))))))
                                              (mul (Pervasives.succ 0)
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0)))))))))
                                              s0)),(Pervasives.succ
                                         idx4)),(test_cache_add_nat.addE c0
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0)))))))))
                                       in
                                       let idx5 =
                                         let _,y = let x,_ = a4 in x in y
                                       in
                                       let ce = let _,y = a4 in y in
                                       if Nat.ltb idx5 sz
                                       then Some
                                              (((CstructBytestring.set_nth sz
                                                  (let x,_ = let x,_ = a4 in x
                                                   in
                                                   x) idx5
                                                  (Int64Word.split2'
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0))))))))
                                                    (mul (Pervasives.succ 0)
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      0))))))))) s0)),(Pervasives.succ
                                              idx5)),(test_cache_add_nat.addE
                                                       ce (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       0))))))))))
                                       else None
                                  else None
                             else None
                        else None with
                  | Some a2 ->
                    let idx3 = let _,y = let x,_ = a2 in x in y in
                    if Nat.ltb idx3 sz
                    then let a3 =
                           ((CstructBytestring.set_nth sz
                              (let x,_ = let x,_ = a2 in x in x) idx3
                              (Int64Word.combine (Pervasives.succ 0)
                                (Int64Word.ws (r.nS, 0, (Int64Word.w0)))
                                (add (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ 0))) (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ 0)))))
                                (Int64Word.combine (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ 0)))
                                  (Int64Word.wzero (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ 0))))
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ 0))))
                                  (Int64Word.natToWord (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0))))
                                    (add (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ 0)))))
                                      (length r.options0)))))),(Pervasives.succ
                           idx3)),(test_cache_add_nat.addE
                                    (let _,y = a2 in y) (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0)))))))))
                         in
                         let idx4 = let _,y = let x,_ = a3 in x in y in
                         if Nat.ltb idx4 sz
                         then let a4 =
                                ((CstructBytestring.set_nth sz
                                   (let x,_ = let x,_ = a3 in x in x) idx4
                                   (Int64Word.combine (Pervasives.succ 0)
                                     (Int64Word.ws (r.fIN, 0,
                                     (Int64Word.w0)))
                                     (add (Pervasives.succ 0)
                                       (add (Pervasives.succ 0)
                                         (add (Pervasives.succ 0)
                                           (add (Pervasives.succ 0)
                                             (add (Pervasives.succ 0)
                                               (add (Pervasives.succ 0)
                                                 (Pervasives.succ 0)))))))
                                     (Int64Word.combine (Pervasives.succ 0)
                                       (Int64Word.ws (r.sYN, 0,
                                       (Int64Word.w0)))
                                       (add (Pervasives.succ 0)
                                         (add (Pervasives.succ 0)
                                           (add (Pervasives.succ 0)
                                             (add (Pervasives.succ 0)
                                               (add (Pervasives.succ 0)
                                                 (Pervasives.succ 0))))))
                                       (Int64Word.combine (Pervasives.succ 0)
                                         (Int64Word.ws (r.rST, 0,
                                         (Int64Word.w0)))
                                         (add (Pervasives.succ 0)
                                           (add (Pervasives.succ 0)
                                             (add (Pervasives.succ 0)
                                               (add (Pervasives.succ 0)
                                                 (Pervasives.succ 0)))))
                                         (Int64Word.combine (Pervasives.succ
                                           0) (Int64Word.ws (r.pSH, 0,
                                           (Int64Word.w0)))
                                           (add (Pervasives.succ 0)
                                             (add (Pervasives.succ 0)
                                               (add (Pervasives.succ 0)
                                                 (Pervasives.succ 0))))
                                           (Int64Word.combine
                                             (Pervasives.succ 0)
                                             (Int64Word.ws (r.aCK, 0,
                                             (Int64Word.w0)))
                                             (add (Pervasives.succ 0)
                                               (add (Pervasives.succ 0)
                                                 (Pervasives.succ 0)))
                                             (Int64Word.combine
                                               (Pervasives.succ 0)
                                               (Int64Word.ws
                                               ((match r.urgentPointer with
                                                 | Some _ -> true
                                                 | None -> false), 0,
                                               (Int64Word.w0)))
                                               (add (Pervasives.succ 0)
                                                 (Pervasives.succ 0))
                                               (Int64Word.combine
                                                 (Pervasives.succ 0)
                                                 (Int64Word.ws (r.eCE, 0,
                                                 (Int64Word.w0)))
                                                 (Pervasives.succ 0)
                                                 (Int64Word.ws (r.cWR, 0,
                                                 (Int64Word.w0))))))))))),(Pervasives.succ
                                idx4)),(test_cache_add_nat.addE
                                         (let _,y = a3 in y) (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ 0)))))))))
                              in
                              let idx5 = let _,y = let x,_ = a4 in x in y in
                              let w = r.windowSize in
                              if Nat.ltb idx5 sz
                              then let a5 =
                                     ((CstructBytestring.set_nth sz
                                        (let x,_ = let x,_ = a4 in x in x)
                                        idx5
                                        (Int64Word.split1' (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ 0))))))))
                                          (mul (Pervasives.succ 0)
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            0))))))))) w)),(Pervasives.succ
                                     idx5)),(test_cache_add_nat.addE
                                              (let _,y = a4 in y)
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0)))))))))
                                   in
                                   let idx6 = let _,y = let x,_ = a5 in x in y
                                   in
                                   let ce = let _,y = a5 in y in
                                   if Nat.ltb idx6 sz
                                   then Some
                                          (((CstructBytestring.set_nth sz
                                              (let x,_ = let x,_ = a5 in x in
                                               x) idx6
                                              (Int64Word.split2'
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0))))))))
                                                (mul (Pervasives.succ 0)
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0)))))))))
                                                w)),(Pervasives.succ
                                          idx6)),(test_cache_add_nat.addE ce
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ 0))))))))))
                                   else None
                              else None
                         else None
                    else None
                  | None -> None)
               | None -> None)
            | None -> None)
         | None -> None) with
  | Some a ->
    let idx = let _,y = let x,_ = a in x in y in
    if Nat.ltb idx sz
    then let a0 =
           ((CstructBytestring.set_nth sz (let x,_ = let x,_ = a in x in x)
              idx
              (Int64Word.wzero (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))),(Pervasives.succ
           idx)),(test_cache_add_nat.addE (let _,y = a in y) (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ 0)))))))))
         in
         let idx0 = let _,y = let x,_ = a0 in x in y in
         if Nat.ltb idx0 sz
         then let a1 =
                ((CstructBytestring.set_nth sz
                   (let x,_ = let x,_ = a0 in x in x) idx0
                   (Int64Word.wzero (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     0)))))))))),(Pervasives.succ
                idx0)),(test_cache_add_nat.addE (let _,y = a0 in y)
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ 0)))))))))
              in
              (match match aligned_option_encode test_cache
                             (fun n0 v0 idx1 w c ->
                             if Nat.ltb idx1 n0
                             then let a2 =
                                    ((CstructBytestring.set_nth n0 v0 idx1
                                       (Int64Word.split1' (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ 0))))))))
                                         (mul (Pervasives.succ 0)
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           0))))))))) w)),(Pervasives.succ
                                    idx1)),(test_cache_add_nat.addE c
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0)))))))))
                                  in
                                  let idx2 = let _,y = let x,_ = a2 in x in y
                                  in
                                  let ce = let _,y = a2 in y in
                                  if Nat.ltb idx2 n0
                                  then Some
                                         (((CstructBytestring.set_nth n0
                                             (let x,_ = let x,_ = a2 in x in x)
                                             idx2
                                             (Int64Word.split2'
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0))))))))
                                               (mul (Pervasives.succ 0)
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ 0)))))))))
                                               w)),(Pervasives.succ
                                         idx2)),(test_cache_add_nat.addE ce
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0))))))))))
                                  else None
                             else None) (fun n0 v0 idx1 _ env ->
                             let w =
                               Int64Word.wzero (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ 0))))))))))))))))
                             in
                             if Nat.ltb idx1 n0
                             then let a2 =
                                    ((CstructBytestring.set_nth n0 v0 idx1
                                       (Int64Word.split1' (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ 0))))))))
                                         (mul (Pervasives.succ 0)
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           0))))))))) w)),(Pervasives.succ
                                    idx1)),(test_cache_add_nat.addE env
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0)))))))))
                                  in
                                  let idx2 = let _,y = let x,_ = a2 in x in y
                                  in
                                  let ce = let _,y = a2 in y in
                                  if Nat.ltb idx2 n0
                                  then Some
                                         (((CstructBytestring.set_nth n0
                                             (let x,_ = let x,_ = a2 in x in x)
                                             idx2
                                             (Int64Word.split2'
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0))))))))
                                               (mul (Pervasives.succ 0)
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ 0)))))))))
                                               w)),(Pervasives.succ
                                         idx2)),(test_cache_add_nat.addE ce
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0))))))))))
                                  else None
                             else None) sz (let x,_ = let x,_ = a1 in x in x)
                             (let _,y = let x,_ = a1 in x in y)
                             r.urgentPointer (let _,y = a1 in y) with
                     | Some a2 ->
                       (match alignedEncodeList test_cache
                                (fun n0 v0 idx1 w c ->
                                if Nat.ltb idx1 n0
                                then let a3 =
                                       ((CstructBytestring.set_nth n0 v0 idx1
                                          (Int64Word.split1' (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ 0))))))))
                                            (mul (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0)))
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                                       idx1)),(test_cache_add_nat.addE c
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0)))))))))
                                     in
                                     let idx2 =
                                       let _,y = let x,_ = a3 in x in y
                                     in
                                     let s =
                                       Int64Word.split2' (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ (Pervasives.succ
                                         (Pervasives.succ 0))))))))
                                         (mul (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           0))) (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ (Pervasives.succ
                                           (Pervasives.succ 0))))))))) w
                                     in
                                     let c0 = let _,y = a3 in y in
                                     if Nat.ltb idx2 n0
                                     then let a4 =
                                            ((CstructBytestring.set_nth n0
                                               (let x,_ = let x,_ = a3 in x in
                                                x) idx2
                                               (Int64Word.split1'
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ
                                                 (Pervasives.succ 0))))))))
                                                 (mul (Pervasives.succ
                                                   (Pervasives.succ 0))
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ 0)))))))))
                                                 s)),(Pervasives.succ
                                            idx2)),(test_cache_add_nat.addE
                                                     c0 (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     (Pervasives.succ
                                                     0)))))))))
                                          in
                                          let idx3 =
                                            let _,y = let x,_ = a4 in x in y
                                          in
                                          let s0 =
                                            Int64Word.split2'
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ
                                              (Pervasives.succ 0))))))))
                                              (mul (Pervasives.succ
                                                (Pervasives.succ 0))
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0))))))))) s
                                          in
                                          let c1 = let _,y = a4 in y in
                                          if Nat.ltb idx3 n0
                                          then let a5 =
                                                 ((CstructBytestring.set_nth
                                                    n0
                                                    (let x,_ =
                                                       let x,_ = a4 in x
                                                     in
                                                     x) idx3
                                                    (Int64Word.split1'
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      (Pervasives.succ
                                                      0))))))))
                                                      (mul (Pervasives.succ
                                                        0) (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        (Pervasives.succ
                                                        0))))))))) s0)),(Pervasives.succ
                                                 idx3)),(test_cache_add_nat.addE
                                                          c1 (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          0)))))))))
                                               in
                                               let idx4 =
                                                 let _,y = let x,_ = a5 in x
                                                 in
                                                 y
                                               in
                                               let ce = let _,y = a5 in y in
                                               if Nat.ltb idx4 n0
                                               then Some
                                                      (((CstructBytestring.set_nth
                                                          n0
                                                          (let x,_ =
                                                             let x,_ = a5 in x
                                                           in
                                                           x) idx4
                                                          (Int64Word.split2'
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0))))))))
                                                            (mul
                                                              (Pervasives.succ
                                                              0)
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              (Pervasives.succ
                                                              0))))))))) s0)),(Pervasives.succ
                                                      idx4)),(test_cache_add_nat.addE
                                                               ce
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               (Pervasives.succ
                                                               0))))))))))
                                               else None
                                          else None
                                     else None
                                else None) sz
                                (let x,_ = let x,_ = a2 in x in x)
                                (let _,y = let x,_ = a2 in x in y) r.options0
                                (let _,y = a2 in y) with
                        | Some a3 ->
                          alignedEncodeByteBuffer test_cache
                            test_cache_add_nat sz
                            (let x,_ = let x,_ = a3 in x in x)
                            (let _,y = let x,_ = a3 in x in y) r.payload
                            (let _,y = a3 in y)
                        | None -> None)
                     | None -> None with
               | Some a2 ->
                 calculate_PseudoChecksum sz srcAddr destAddr tcpLength
                   (Int64Word.natToWord (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     0)))))))) (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ 0))))))) (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   0)))))))))))))))) (let x,_ = let x,_ = a2 in x in x)
                   (let _,y = let x,_ = a2 in x in y) r (let _,y = a2 in y)
               | None -> None)
         else None
    else None
  | None -> None

(** val tCP_decoder_impl :
    CstructBytestring.storage_t -> CstructBytestring.storage_t -> Int64Word.t
    -> OCamlNativeInt.t -> CstructBytestring.storage_t ->
    ((tCP_Packet*OCamlNativeInt.t)*unit) option **)

let tCP_decoder_impl srcAddr destAddr tcpLength sz v =
  if Int64Word.weq (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))))
       (pseudoHeader_checksum' srcAddr destAddr tcpLength
         (Int64Word.natToWord (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))) sz v)
       (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0)))))))))))))), (Int64Word.ws
       (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0)))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))), (Int64Word.ws (true, (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0)))))))))), (Int64Word.ws (true, (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0)))))))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
       (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0)))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
       (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
       (true, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (true,
       (Pervasives.succ 0), (Int64Word.ws (true, 0,
       (Int64Word.w0)))))))))))))))))))))))))))))))))
  then let idx = Obj.magic 0 in
       let c = Obj.magic () in
       (match CstructBytestring.nth_opt sz v idx with
        | Some a ->
          let a0 = (a,(Pervasives.succ
            idx)),(test_cache_add_nat.addD c (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ 0)))))))))
          in
          let idx0 = let _,y = let x,_ = a0 in x in y in
          (match CstructBytestring.nth_opt sz v idx0 with
           | Some a1 ->
             let a2 = (a1,(Pervasives.succ
               idx0)),(test_cache_add_nat.addD (let _,y = a0 in y)
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ 0)))))))))
             in
             let a3 =
               ((Int64Word.append (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  0)))))))) (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  0)))))))) (let x,_ = let x,_ = a2 in x in x)
                  (let x,_ = let x,_ = a0 in x in x)),(let _,y =
                                                         let x,_ = a2 in x
                                                       in
                                                       y)),(let _,y = a2 in y)
             in
             let idx1 = let _,y = let x,_ = a3 in x in y in
             (match CstructBytestring.nth_opt sz v idx1 with
              | Some a4 ->
                let a5 = (a4,(Pervasives.succ
                  idx1)),(test_cache_add_nat.addD (let _,y = a3 in y)
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ 0)))))))))
                in
                let idx2 = let _,y = let x,_ = a5 in x in y in
                (match CstructBytestring.nth_opt sz v idx2 with
                 | Some a6 ->
                   let a7 = (a6,(Pervasives.succ
                     idx2)),(test_cache_add_nat.addD (let _,y = a5 in y)
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ 0)))))))))
                   in
                   let a8 =
                     ((Int64Word.append (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        0)))))))) (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        0)))))))) (let x,_ = let x,_ = a7 in x in x)
                        (let x,_ = let x,_ = a5 in x in x)),(let _,y =
                                                               let x,_ = a7 in
                                                               x
                                                             in
                                                             y)),(let _,y = a7
                                                                  in
                                                                  y)
                   in
                   let idx3 = let _,y = let x,_ = a8 in x in y in
                   (match CstructBytestring.nth_opt sz v idx3 with
                    | Some a9 ->
                      let a10 = (a9,(Pervasives.succ
                        idx3)),(test_cache_add_nat.addD (let _,y = a8 in y)
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ 0)))))))))
                      in
                      let idx4 = let _,y = let x,_ = a10 in x in y in
                      (match CstructBytestring.nth_opt sz v idx4 with
                       | Some a11 ->
                         let a12 = (a11,(Pervasives.succ
                           idx4)),(test_cache_add_nat.addD
                                    (let _,y = a10 in y) (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0)))))))))
                         in
                         let idx5 = let _,y = let x,_ = a12 in x in y in
                         (match CstructBytestring.nth_opt sz v idx5 with
                          | Some a13 ->
                            let a14 = (a13,(Pervasives.succ
                              idx5)),(test_cache_add_nat.addD
                                       (let _,y = a12 in y) (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ 0)))))))))
                            in
                            let idx6 = let _,y = let x,_ = a14 in x in y in
                            (match CstructBytestring.nth_opt sz v idx6 with
                             | Some a15 ->
                               let a16 = (a15,(Pervasives.succ
                                 idx6)),(test_cache_add_nat.addD
                                          (let _,y = a14 in y)
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0)))))))))
                               in
                               let a17 =
                                 ((Int64Word.append (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0))))))))
                                    (add (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      0))))))))
                                      (add (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        0)))))))) (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ 0))))))))))
                                    (let x,_ = let x,_ = a16 in x in x)
                                    (Int64Word.append (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ 0))))))))
                                      (add (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        0)))))))) (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ 0)))))))))
                                      (let x,_ = let x,_ = a14 in x in x)
                                      (Int64Word.append (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ 0))))))))
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        (Pervasives.succ (Pervasives.succ
                                        0))))))))
                                        (let x,_ = let x,_ = a12 in x in x)
                                        (let x,_ = let x,_ = a10 in x in x)))),
                                 (let _,y = let x,_ = a16 in x in y)),
                                 (let _,y = a16 in y)
                               in
                               let idx7 = let _,y = let x,_ = a17 in x in y in
                               (match CstructBytestring.nth_opt sz v idx7 with
                                | Some a18 ->
                                  let a19 = (a18,(Pervasives.succ
                                    idx7)),(test_cache_add_nat.addD
                                             (let _,y = a17 in y)
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ
                                             (Pervasives.succ 0)))))))))
                                  in
                                  let idx8 = let _,y = let x,_ = a19 in x in y
                                  in
                                  (match CstructBytestring.nth_opt sz v idx8 with
                                   | Some a20 ->
                                     let a21 = (a20,(Pervasives.succ
                                       idx8)),(test_cache_add_nat.addD
                                                (let _,y = a19 in y)
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0)))))))))
                                     in
                                     let idx9 =
                                       let _,y = let x,_ = a21 in x in y
                                     in
                                     (match CstructBytestring.nth_opt sz v
                                              idx9 with
                                      | Some a22 ->
                                        let a23 = (a22,(Pervasives.succ
                                          idx9)),(test_cache_add_nat.addD
                                                   (let _,y = a21 in y)
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ
                                                   (Pervasives.succ 0)))))))))
                                        in
                                        let idx10 =
                                          let _,y = let x,_ = a23 in x in y
                                        in
                                        (match CstructBytestring.nth_opt sz v
                                                 idx10 with
                                         | Some a24 ->
                                           let a25 = (a24,(Pervasives.succ
                                             idx10)),(test_cache_add_nat.addD
                                                       (let _,y = a23 in y)
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       (Pervasives.succ
                                                       0)))))))))
                                           in
                                           let a26 =
                                             ((Int64Word.append
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ
                                                (Pervasives.succ 0))))))))
                                                (add (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0))))))))
                                                  (add (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0))))))))
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0))))))))))
                                                (let x,_ = let x,_ = a25 in x
                                                 in
                                                 x)
                                                (Int64Word.append
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ
                                                  (Pervasives.succ 0))))))))
                                                  (add (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0))))))))
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0)))))))))
                                                  (let x,_ =
                                                     let x,_ = a23 in x
                                                   in
                                                   x)
                                                  (Int64Word.append
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0))))))))
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    (Pervasives.succ
                                                    0))))))))
                                                    (let x,_ =
                                                       let x,_ = a21 in x
                                                     in
                                                     x)
                                                    (let x,_ =
                                                       let x,_ = a19 in x
                                                     in
                                                     x)))),(let _,y =
                                                              let x,_ = a25 in
                                                              x
                                                            in
                                                            y)),(let _,y = a25
                                                                 in
                                                                 y)
                                           in
                                           let idx11 =
                                             let _,y = let x,_ = a26 in x in y
                                           in
                                           (match CstructBytestring.nth_opt
                                                    sz v idx11 with
                                            | Some a27 ->
                                              let a28 = (a27,(Pervasives.succ
                                                idx11)),(test_cache_add_nat.addD
                                                          (let _,y = a26 in y)
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          (Pervasives.succ
                                                          0)))))))))
                                              in
                                              let b =
                                                let x,_ = let x,_ = a28 in x
                                                in
                                                x
                                              in
                                              let idx12 =
                                                let _,y = let x,_ = a28 in x
                                                in
                                                y
                                              in
                                              (match CstructBytestring.nth_opt
                                                       sz v idx12 with
                                               | Some a29 ->
                                                 let a30 =
                                                   (a29,(Pervasives.succ
                                                   idx12)),(test_cache_add_nat.addD
                                                             (let _,y = a28 in
                                                              y)
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             (Pervasives.succ
                                                             0)))))))))
                                                 in
                                                 let b0 =
                                                   let x,_ =
                                                     let x,_ = a30 in x
                                                   in
                                                   x
                                                 in
                                                 let idx13 =
                                                   let _,y =
                                                     let x,_ = a30 in x
                                                   in
                                                   y
                                                 in
                                                 (match CstructBytestring.nth_opt
                                                          sz v idx13 with
                                                  | Some a31 ->
                                                    let a32 =
                                                      (a31,(Pervasives.succ
                                                      idx13)),(test_cache_add_nat.addD
                                                                (let _,y = a30
                                                                 in
                                                                 y)
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                (Pervasives.succ
                                                                0)))))))))
                                                    in
                                                    let idx14 =
                                                      let _,y =
                                                        let x,_ = a32 in x
                                                      in
                                                      y
                                                    in
                                                    (match CstructBytestring.nth_opt
                                                             sz v idx14 with
                                                     | Some a33 ->
                                                       let a34 =
                                                         (a33,(Pervasives.succ
                                                         idx14)),(test_cache_add_nat.addD
                                                                   (let _,y =
                                                                    a32
                                                                    in
                                                                    y)
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   (Pervasives.succ
                                                                   0)))))))))
                                                       in
                                                       let a35 =
                                                         ((Int64Word.append
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0))))))))
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            (Pervasives.succ
                                                            0))))))))
                                                            (let x,_ =
                                                               let x,_ = a34
                                                               in
                                                               x
                                                             in
                                                             x)
                                                            (let x,_ =
                                                               let x,_ = a32
                                                               in
                                                               x
                                                             in
                                                             x)),(let _,y =
                                                                    let x,_ =
                                                                    a34
                                                                    in
                                                                    x
                                                                  in
                                                                  y)),
                                                         (let _,y = a34 in y)
                                                       in
                                                       (match skipCurrentByte
                                                                test_cache
                                                                test_cache_add_nat
                                                                sz v
                                                                (let _,y =
                                                                   let x,_ =
                                                                    a35
                                                                   in
                                                                   x
                                                                 in
                                                                 y)
                                                                (let _,y = a35
                                                                 in
                                                                 y) with
                                                        | Some a36 ->
                                                          (match skipCurrentByte
                                                                   test_cache
                                                                   test_cache_add_nat
                                                                   sz v
                                                                   (let _,y =
                                                                    let x,_ =
                                                                    a36
                                                                    in
                                                                    x
                                                                    in
                                                                    y)
                                                                   (let _,y =
                                                                    a36
                                                                    in
                                                                    y) with
                                                           | Some a37 ->
                                                             (match aligned_option_decode
                                                                    test_cache
                                                                    (fun numBytes v0 idx15 c0 ->
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    numBytes
                                                                    v0 idx15 with
                                                                    | Some a38 ->
                                                                    let a39 =
                                                                    (a38,(Pervasives.succ
                                                                    idx15)),
                                                                    (test_cache_add_nat.addD
                                                                    c0
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let idx16 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a39
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    (
                                                                    match 
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    numBytes
                                                                    v0 idx16 with
                                                                    | Some a40 ->
                                                                    let a41 =
                                                                    (a40,(Pervasives.succ
                                                                    idx16)),
                                                                    (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a39
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let a42 =
                                                                    ((Int64Word.w0),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a41
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a41
                                                                    in
                                                                    y)
                                                                    in
                                                                    Some
                                                                    ((
                                                                    (Int64Word.append
                                                                    (mul 0
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a42
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a41
                                                                    in
                                                                    x
                                                                    in
                                                                    x)),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a42
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a42
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None with
                                                                    | Some a40 ->
                                                                    Some
                                                                    (((Int64Word.append
                                                                    (mul
                                                                    (Pervasives.succ
                                                                    0)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a40
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a39
                                                                    in
                                                                    x
                                                                    in
                                                                    x)),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a40
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a40
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None)
                                                                    | None ->
                                                                    None)
                                                                    (fun numBytes v0 idx15 c0 ->
                                                                    match 
                                                                    skipCurrentByte
                                                                    test_cache
                                                                    test_cache_add_nat
                                                                    numBytes
                                                                    v0 idx15
                                                                    c0 with
                                                                    | Some a38 ->
                                                                    (match 
                                                                    match 
                                                                    skipCurrentByte
                                                                    test_cache
                                                                    test_cache_add_nat
                                                                    numBytes
                                                                    v0
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a38
                                                                    in
                                                                    x
                                                                    in
                                                                    y)
                                                                    (
                                                                    let _,y =
                                                                    a38
                                                                    in
                                                                    y) with
                                                                    | Some a39 ->
                                                                    let a40 =
                                                                    ((),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a39
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a39
                                                                    in
                                                                    y)
                                                                    in
                                                                    Some
                                                                    (((),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a40
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a40
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None with
                                                                    | Some a39 ->
                                                                    Some
                                                                    (((),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a39
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a39
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None)
                                                                    | None ->
                                                                    None)
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b0))))))
                                                                    sz v
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a37
                                                                    in
                                                                    x
                                                                    in
                                                                    y)
                                                                    (
                                                                    let _,y =
                                                                    a37
                                                                    in
                                                                    y) with
                                                              | Some a38 ->
                                                                let a39 =
                                                                  let x,_ =
                                                                    let x,_ =
                                                                    a38
                                                                    in
                                                                    x
                                                                  in
                                                                  x
                                                                in
                                                                (match 
                                                                 listAlignedDecodeM
                                                                   test_cache
                                                                   sz
                                                                   (fun numBytes v0 idx15 c0 ->
                                                                   match 
                                                                   CstructBytestring.nth_opt
                                                                    numBytes
                                                                    v0 idx15 with
                                                                   | Some a40 ->
                                                                    let a41 =
                                                                    (a40,(Pervasives.succ
                                                                    idx15)),
                                                                    (test_cache_add_nat.addD
                                                                    c0
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let idx16 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a41
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    (
                                                                    match 
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    numBytes
                                                                    v0 idx16 with
                                                                    | Some a42 ->
                                                                    let a43 =
                                                                    (a42,(Pervasives.succ
                                                                    idx16)),
                                                                    (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a41
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let idx17 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a43
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    (
                                                                    match 
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    numBytes
                                                                    v0 idx17 with
                                                                    | Some a44 ->
                                                                    let a45 =
                                                                    (a44,(Pervasives.succ
                                                                    idx17)),
                                                                    (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a43
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let idx18 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a45
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    (
                                                                    match 
                                                                    match 
                                                                    CstructBytestring.nth_opt
                                                                    numBytes
                                                                    v0 idx18 with
                                                                    | Some a46 ->
                                                                    let a47 =
                                                                    (a46,(Pervasives.succ
                                                                    idx18)),
                                                                    (test_cache_add_nat.addD
                                                                    (
                                                                    let _,y =
                                                                    a45
                                                                    in
                                                                    y)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    in
                                                                    let a48 =
                                                                    ((Int64Word.w0),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a47
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a47
                                                                    in
                                                                    y)
                                                                    in
                                                                    Some
                                                                    ((
                                                                    (Int64Word.append
                                                                    (mul 0
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a48
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a47
                                                                    in
                                                                    x
                                                                    in
                                                                    x)),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a48
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a48
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None with
                                                                    | Some a46 ->
                                                                    Some
                                                                    (((Int64Word.append
                                                                    (mul
                                                                    (Pervasives.succ
                                                                    0)
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a46
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a45
                                                                    in
                                                                    x
                                                                    in
                                                                    x)),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a46
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a46
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None)
                                                                    | None ->
                                                                    None with
                                                                    | Some a44 ->
                                                                    Some
                                                                    (((Int64Word.append
                                                                    (mul
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a44
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a43
                                                                    in
                                                                    x
                                                                    in
                                                                    x)),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a44
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a44
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None)
                                                                    | None ->
                                                                    None with
                                                                    | Some a42 ->
                                                                    Some
                                                                    (((Int64Word.append
                                                                    (mul
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a42
                                                                    in
                                                                    x
                                                                    in
                                                                    x)
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a41
                                                                    in
                                                                    x
                                                                    in
                                                                    x)),
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a42
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                                                                    (
                                                                    let _,y =
                                                                    a42
                                                                    in
                                                                    y))
                                                                    | None ->
                                                                    None)
                                                                   | None ->
                                                                    None)
                                                                   (sub
                                                                    (Int64Word.wordToNat
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.split1'
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (id
                                                                    (Int64Word.split1'
                                                                    (add
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    0) b))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))) v
                                                                   (let _,y =
                                                                    let x,_ =
                                                                    a38
                                                                    in
                                                                    x
                                                                    in
                                                                    y)
                                                                   (let _,y =
                                                                    a38
                                                                    in
                                                                    y) with
                                                                 | Some a40 ->
                                                                   let l =
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a40
                                                                    in
                                                                    x
                                                                    in
                                                                    x
                                                                   in
                                                                   (match 
                                                                    byteBufferAlignedDecodeM
                                                                    test_cache
                                                                    test_cache_add_nat
                                                                    sz
                                                                    (sub
                                                                    (Int64Word.wordToNat
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
                                                                    (Pervasives.succ
                                                                    0))))))))))))))))
                                                                    tcpLength)
                                                                    (add
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
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))))))))))))))
                                                                    (mul
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (sub
                                                                    (Int64Word.wordToNat
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.split1'
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (id
                                                                    (Int64Word.split1'
                                                                    (add
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    0) b))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))))
                                                                    v
                                                                    (
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a40
                                                                    in
                                                                    x
                                                                    in
                                                                    y)
                                                                    (
                                                                    let _,y =
                                                                    a40
                                                                    in
                                                                    y) with
                                                                    | Some a41 ->
                                                                    let b1 =
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a41
                                                                    in
                                                                    x
                                                                    in
                                                                    x
                                                                    in
                                                                    let idx15 =
                                                                    let _,y =
                                                                    let x,_ =
                                                                    a41
                                                                    in
                                                                    x
                                                                    in
                                                                    y
                                                                    in
                                                                    let c0 =
                                                                    let _,y =
                                                                    a41
                                                                    in
                                                                    y
                                                                    in
                                                                    if 
                                                                    (&&)
                                                                    ((&&)
                                                                    ((&&)
                                                                    (if 
                                                                    (<)
                                                                    (length l)
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
                                                                    then true
                                                                    else false)
                                                                    ((=)
                                                                    (Int64Word.wordToNat
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
                                                                    (Pervasives.succ
                                                                    0))))))))))))))))
                                                                    tcpLength)
                                                                    (add
                                                                    (add
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
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))))))))))))))))
                                                                    (mul
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (length l)))
                                                                    (projT1
                                                                    b1))))
                                                                    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun m' ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun m'0 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun m'1 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun m'2 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun m'3 ->
                                                                    (=)
                                                                    (length l)
                                                                    m'3)
                                                                    m'2)
                                                                    m'1)
                                                                    m'0)
                                                                    m')
                                                                    (Int64Word.wordToNat
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.split1'
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (id
                                                                    (Int64Word.split1'
                                                                    (add
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Pervasives.succ
                                                                    0) b))))))
                                                                    (eqb
                                                                    (match a39 with
                                                                    | Some _ ->
                                                                    true
                                                                    | None ->
                                                                    false)
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b0)))))))
                                                                    then 
                                                                    Obj.magic
                                                                    (Some
                                                                    (({ sourcePort =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a3
                                                                    in
                                                                    x
                                                                    in
                                                                    x);
                                                                    destPort =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a8
                                                                    in
                                                                    x
                                                                    in
                                                                    x);
                                                                    seqNumber =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a17
                                                                    in
                                                                    x
                                                                    in
                                                                    x);
                                                                    ackNumber =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a26
                                                                    in
                                                                    x
                                                                    in
                                                                    x); nS =
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b); cWR =
                                                                    (Int64Word.whd
                                                                    0
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    0)
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b0))))))));
                                                                    eCE =
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    0)
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b0)))))));
                                                                    aCK =
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b0)))));
                                                                    pSH =
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b0))));
                                                                    rST =
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b0)));
                                                                    sYN =
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0))))))
                                                                    (Int64Word.wtl
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b0));
                                                                    fIN =
                                                                    (Int64Word.whd
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    (Pervasives.succ
                                                                    0)))))))
                                                                    b0);
                                                                    windowSize =
                                                                    (
                                                                    let x,_ =
                                                                    let x,_ =
                                                                    a35
                                                                    in
                                                                    x
                                                                    in
                                                                    x);
                                                                    urgentPointer =
                                                                    a39;
                                                                    options0 =
                                                                    l;
                                                                    payload =
                                                                    b1 },idx15),c0))
                                                                    else 
                                                                    Obj.magic
                                                                    None
                                                                    | None ->
                                                                    Obj.magic
                                                                    None)
                                                                 | None ->
                                                                   Obj.magic
                                                                    None)
                                                              | None ->
                                                                Obj.magic None)
                                                           | None ->
                                                             Obj.magic None)
                                                        | None ->
                                                          Obj.magic None)
                                                     | None -> Obj.magic None)
                                                  | None -> Obj.magic None)
                                               | None -> Obj.magic None)
                                            | None -> Obj.magic None)
                                         | None -> Obj.magic None)
                                      | None -> Obj.magic None)
                                   | None -> Obj.magic None)
                                | None -> Obj.magic None)
                             | None -> Obj.magic None)
                          | None -> Obj.magic None)
                       | None -> Obj.magic None)
                    | None -> Obj.magic None)
                 | None -> Obj.magic None)
              | None -> Obj.magic None)
           | None -> Obj.magic None)
        | None -> Obj.magic None)
  else Obj.magic None

type uDP_Packet = { sourcePort0 : Int64Word.t; destPort0 : Int64Word.t;
                    payload0 : (OCamlNativeInt.t,
                               CstructBytestring.storage_t) sigT }

(** val sourcePort0 : uDP_Packet -> Int64Word.t **)

let sourcePort0 x = x.sourcePort0

(** val destPort0 : uDP_Packet -> Int64Word.t **)

let destPort0 x = x.destPort0

(** val payload0 :
    uDP_Packet -> (OCamlNativeInt.t, CstructBytestring.storage_t) sigT **)

let payload0 x = x.payload0

(** val uDP_encoder_impl :
    CstructBytestring.storage_t -> CstructBytestring.storage_t -> Int64Word.t
    -> uDP_Packet -> OCamlNativeInt.t -> CstructBytestring.storage_t ->
    ((CstructBytestring.storage_t*OCamlNativeInt.t)*cacheFormat) option **)

let uDP_encoder_impl srcAddr destAddr udpLength r sz v =
  match let idx = 0 in
        (match let w = r.sourcePort0 in
               if Nat.ltb idx sz
               then let a =
                      ((CstructBytestring.set_nth sz v idx
                         (Int64Word.split1' (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           0))))))))
                           (mul (Pervasives.succ 0) (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ (Pervasives.succ
                             (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                      idx)),(test_cache_add_nat.addE (Obj.magic ())
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ 0)))))))))
                    in
                    let idx0 = let _,y = let x,_ = a in x in y in
                    let ce = let _,y = a in y in
                    if Nat.ltb idx0 sz
                    then Some
                           (((CstructBytestring.set_nth sz
                               (let x,_ = let x,_ = a in x in x) idx0
                               (Int64Word.split2' (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ 0))))))))
                                 (mul (Pervasives.succ 0) (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                           idx0)),(test_cache_add_nat.addE ce
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    0))))))))))
                    else None
               else None with
         | Some a ->
           let idx0 = let _,y = let x,_ = a in x in y in
           (match let w = r.destPort0 in
                  if Nat.ltb idx0 sz
                  then let a0 =
                         ((CstructBytestring.set_nth sz
                            (let x,_ = let x,_ = a in x in x) idx0
                            (Int64Word.split1' (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ 0))))))))
                              (mul (Pervasives.succ 0) (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                         idx0)),(test_cache_add_nat.addE (let _,y = a in y)
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ
                                  (Pervasives.succ (Pervasives.succ 0)))))))))
                       in
                       let idx1 = let _,y = let x,_ = a0 in x in y in
                       let ce = let _,y = a0 in y in
                       if Nat.ltb idx1 sz
                       then Some
                              (((CstructBytestring.set_nth sz
                                  (let x,_ = let x,_ = a0 in x in x) idx1
                                  (Int64Word.split2' (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0))))))))
                                    (mul (Pervasives.succ 0) (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ (Pervasives.succ
                                      (Pervasives.succ 0))))))))) w)),(Pervasives.succ
                              idx1)),(test_cache_add_nat.addE ce
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       (Pervasives.succ (Pervasives.succ
                                       0))))))))))
                       else None
                  else None with
            | Some a0 ->
              setCurrentBytes test_cache test_cache_add_nat sz
                (Pervasives.succ (Pervasives.succ 0))
                (let x,_ = let x,_ = a0 in x in x)
                (let _,y = let x,_ = a0 in x in y)
                (Int64Word.natToWord (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ 0))))))))))))))))
                  (add (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ 0))))))))
                    (projT1 r.payload0))) (let _,y = a0 in y)
            | None -> None)
         | None -> None) with
  | Some a ->
    let idx = let _,y = let x,_ = a in x in y in
    if Nat.ltb idx sz
    then let a0 =
           ((CstructBytestring.set_nth sz (let x,_ = let x,_ = a in x in x)
              idx
              (Int64Word.wzero (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ
                (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))),(Pervasives.succ
           idx)),(test_cache_add_nat.addE (let _,y = a in y) (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ 0)))))))))
         in
         let idx0 = let _,y = let x,_ = a0 in x in y in
         if Nat.ltb idx0 sz
         then let a1 =
                ((CstructBytestring.set_nth sz
                   (let x,_ = let x,_ = a0 in x in x) idx0
                   (Int64Word.wzero (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     0)))))))))),(Pervasives.succ
                idx0)),(test_cache_add_nat.addE (let _,y = a0 in y)
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ 0)))))))))
              in
              (match alignedEncodeByteBuffer test_cache test_cache_add_nat sz
                       (let x,_ = let x,_ = a1 in x in x)
                       (let _,y = let x,_ = a1 in x in y) r.payload0
                       (let _,y = a1 in y) with
               | Some a2 ->
                 calculate_PseudoChecksum sz srcAddr destAddr udpLength
                   (Int64Word.natToWord (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     0)))))))) (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     (Pervasives.succ (Pervasives.succ (Pervasives.succ
                     0)))))))))))))))))) (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ (Pervasives.succ (Pervasives.succ
                   (Pervasives.succ 0))))))
                   (let x,_ = let x,_ = a2 in x in x)
                   (let _,y = let x,_ = a2 in x in y) r (let _,y = a2 in y)
               | None -> None)
         else None
    else None
  | None -> None

(** val uDP_decoder_impl :
    CstructBytestring.storage_t -> CstructBytestring.storage_t -> Int64Word.t
    -> OCamlNativeInt.t -> CstructBytestring.storage_t ->
    ((uDP_Packet*OCamlNativeInt.t)*unit) option **)

let uDP_decoder_impl srcAddr destAddr udpLength sz v =
  if Int64Word.weq (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))))
       (pseudoHeader_checksum' srcAddr destAddr udpLength
         (Int64Word.natToWord (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ (Pervasives.succ
           (Pervasives.succ (Pervasives.succ 0)))))))))))))))))) sz v)
       (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))))))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0)))))))))))))), (Int64Word.ws
       (true, (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0))))))))))))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0)))))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0))))))))))), (Int64Word.ws (true, (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ 0)))))))))), (Int64Word.ws (true, (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0))))))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0)))))))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))),
       (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       0)))))), (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))),
       (Int64Word.ws (true, (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ 0)))), (Int64Word.ws (true,
       (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), (Int64Word.ws
       (true, (Pervasives.succ (Pervasives.succ 0)), (Int64Word.ws (true,
       (Pervasives.succ 0), (Int64Word.ws (true, 0,
       (Int64Word.w0)))))))))))))))))))))))))))))))))
  then let idx = Obj.magic 0 in
       let c = Obj.magic () in
       (match CstructBytestring.nth_opt sz v idx with
        | Some a ->
          let a0 = (a,(Pervasives.succ
            idx)),(test_cache_add_nat.addD c (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ 0)))))))))
          in
          let idx0 = let _,y = let x,_ = a0 in x in y in
          (match CstructBytestring.nth_opt sz v idx0 with
           | Some a1 ->
             let a2 = (a1,(Pervasives.succ
               idx0)),(test_cache_add_nat.addD (let _,y = a0 in y)
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ 0)))))))))
             in
             let a3 =
               ((Int64Word.append (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  0)))))))) (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ
                  0)))))))) (let x,_ = let x,_ = a2 in x in x)
                  (let x,_ = let x,_ = a0 in x in x)),(let _,y =
                                                         let x,_ = a2 in x
                                                       in
                                                       y)),(let _,y = a2 in y)
             in
             let idx1 = let _,y = let x,_ = a3 in x in y in
             (match CstructBytestring.nth_opt sz v idx1 with
              | Some a4 ->
                let a5 = (a4,(Pervasives.succ
                  idx1)),(test_cache_add_nat.addD (let _,y = a3 in y)
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ (Pervasives.succ
                           (Pervasives.succ (Pervasives.succ 0)))))))))
                in
                let idx2 = let _,y = let x,_ = a5 in x in y in
                (match CstructBytestring.nth_opt sz v idx2 with
                 | Some a6 ->
                   let a7 = (a6,(Pervasives.succ
                     idx2)),(test_cache_add_nat.addD (let _,y = a5 in y)
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ 0)))))))))
                   in
                   let a8 =
                     ((Int64Word.append (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        0)))))))) (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ (Pervasives.succ (Pervasives.succ
                        0)))))))) (let x,_ = let x,_ = a7 in x in x)
                        (let x,_ = let x,_ = a5 in x in x)),(let _,y =
                                                               let x,_ = a7 in
                                                               x
                                                             in
                                                             y)),(let _,y = a7
                                                                  in
                                                                  y)
                   in
                   let idx3 = let _,y = let x,_ = a8 in x in y in
                   (match CstructBytestring.nth_opt sz v idx3 with
                    | Some a9 ->
                      let a10 = (a9,(Pervasives.succ
                        idx3)),(test_cache_add_nat.addD (let _,y = a8 in y)
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ (Pervasives.succ 0)))))))))
                      in
                      let idx4 = let _,y = let x,_ = a10 in x in y in
                      (match CstructBytestring.nth_opt sz v idx4 with
                       | Some a11 ->
                         let a12 = (a11,(Pervasives.succ
                           idx4)),(test_cache_add_nat.addD
                                    (let _,y = a10 in y) (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ (Pervasives.succ
                                    (Pervasives.succ 0)))))))))
                         in
                         let a13 =
                           ((Int64Word.append (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ 0)))))))) (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ (Pervasives.succ
                              (Pervasives.succ 0))))))))
                              (let x,_ = let x,_ = a12 in x in x)
                              (let x,_ = let x,_ = a10 in x in x)),(let _,y =
                                                                    let x,_ =
                                                                    a12
                                                                    in
                                                                    x
                                                                    in
                                                                    y)),
                           (let _,y = a12 in y)
                         in
                         let w = let x,_ = let x,_ = a13 in x in x in
                         (match skipCurrentByte test_cache test_cache_add_nat
                                  sz v (let _,y = let x,_ = a13 in x in y)
                                  (let _,y = a13 in y) with
                          | Some a14 ->
                            (match skipCurrentByte test_cache
                                     test_cache_add_nat sz v
                                     (let _,y = let x,_ = a14 in x in y)
                                     (let _,y = a14 in y) with
                             | Some a15 ->
                               (match byteBufferAlignedDecodeM test_cache
                                        test_cache_add_nat sz
                                        (sub
                                          (Int64Word.wordToNat
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            0)))))))))))))))) w)
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          (Pervasives.succ (Pervasives.succ
                                          0))))))))) v
                                        (let _,y = let x,_ = a15 in x in y)
                                        (let _,y = a15 in y) with
                                | Some a16 ->
                                  let b = let x,_ = let x,_ = a16 in x in x in
                                  let idx5 = let _,y = let x,_ = a16 in x in y
                                  in
                                  let c0 = let _,y = a16 in y in
                                  if (&&)
                                       (if (<) (projT1 b)
                                             (sub
                                               (pow2 (Pervasives.succ
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
                                                 0)))))))))))))))))
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ
                                               (Pervasives.succ 0)))))))))
                                        then true
                                        else false)
                                       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> false)
                                          (fun m' ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> false)
                                            (fun m'0 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> false)
                                              (fun m'1 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> false)
                                                (fun m'2 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> false)
                                                  (fun m'3 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ ->
                                                    false)
                                                    (fun m'4 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      false)
                                                      (fun m'5 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        false)
                                                        (fun m'6 ->
                                                        (=) (projT1 b) m'6)
                                                        m'5)
                                                      m'4)
                                                    m'3)
                                                  m'2)
                                                m'1)
                                              m'0)
                                            m')
                                          (Int64Word.wordToNat
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            (Pervasives.succ (Pervasives.succ
                                            0)))))))))))))))) w))
                                  then Obj.magic (Some (({ sourcePort0 =
                                         (let x,_ = let x,_ = a3 in x in x);
                                         destPort0 =
                                         (let x,_ = let x,_ = a8 in x in x);
                                         payload0 = b },idx5),c0))
                                  else Obj.magic None
                                | None -> Obj.magic None)
                             | None -> Obj.magic None)
                          | None -> Obj.magic None)
                       | None -> Obj.magic None)
                    | None -> Obj.magic None)
                 | None -> Obj.magic None)
              | None -> Obj.magic None)
           | None -> Obj.magic None)
        | None -> Obj.magic None)
  else Obj.magic None

(** val injectEnum :
    OCamlNativeInt.t -> 'a1 StackVector.t -> ArrayVector.idx_t -> 'a1 **)

let injectEnum =
  StackVector.nth

(** val wrapDecoder :
    OCamlNativeInt.t -> (OCamlNativeInt.t -> CstructBytestring.storage_t ->
    (('a1*OCamlNativeInt.t)*'a2) option) -> CstructBytestring.storage_t ->
    'a1 option **)

let wrapDecoder sz impl bs =
  match impl sz bs with
  | Some p -> let p0,_ = p in let pkt,_ = p0 in Some pkt
  | None -> None

(** val wrapEncoder :
    OCamlNativeInt.t -> (OCamlNativeInt.t -> CstructBytestring.storage_t ->
    'a1 -> ((CstructBytestring.storage_t*OCamlNativeInt.t)*'a2) option) ->
    'a1 -> CstructBytestring.storage_t -> CstructBytestring.storage_t option **)

let wrapEncoder sz impl pkt out =
  match impl sz out pkt with
  | Some p -> let p0,_ = p in let out0,_ = p0 in Some out0
  | None -> None

(** val fiat_ethernet_encode :
    OCamlNativeInt.t -> ethernetHeader -> CstructBytestring.storage_t ->
    CstructBytestring.storage_t option **)

let fiat_ethernet_encode sz =
  wrapEncoder sz (fun sz0 v pkt -> ethernetHeader_encoder_impl pkt sz0 v)

(** val fiat_ethernet_decode :
    OCamlNativeInt.t -> CstructBytestring.storage_t -> OCamlNativeInt.t ->
    ethernetHeader option **)

let fiat_ethernet_decode sz v packet_length =
  wrapDecoder sz (ethernet_decoder_impl packet_length) v

(** val fiat_arp_decode :
    OCamlNativeInt.t -> CstructBytestring.storage_t -> aRPPacket option **)

let fiat_arp_decode sz =
  wrapDecoder sz aRP_decoder_impl

(** val fiat_arp_encode :
    OCamlNativeInt.t -> aRPPacket -> CstructBytestring.storage_t ->
    CstructBytestring.storage_t option **)

let fiat_arp_encode sz =
  wrapEncoder sz aRP_encoder_impl

(** val fiat_ipv4_decode :
    OCamlNativeInt.t -> CstructBytestring.storage_t -> iPv4_Packet option **)

let fiat_ipv4_decode sz =
  wrapDecoder sz iPv4_decoder_impl

(** val fiat_ipv4_encode :
    OCamlNativeInt.t -> iPv4_Packet -> CstructBytestring.storage_t ->
    CstructBytestring.storage_t option **)

let fiat_ipv4_encode sz =
  wrapEncoder sz iPv4_encoder_impl

(** val fiat_tcp_encode :
    OCamlNativeInt.t -> tCP_Packet -> CstructBytestring.storage_t ->
    CstructBytestring.storage_t -> Int64Word.t -> CstructBytestring.storage_t
    -> CstructBytestring.storage_t option **)

let fiat_tcp_encode sz v srcAddress dstAddress tcpLength =
  wrapEncoder sz (fun sz0 v0 pkt ->
    tCP_encoder_impl srcAddress dstAddress tcpLength pkt sz0 v0) v

(** val fiat_tcp_decode :
    OCamlNativeInt.t -> CstructBytestring.storage_t -> Int64Word.t
    StackVector.t -> Int64Word.t StackVector.t -> Int64Word.t -> tCP_Packet
    option **)

let fiat_tcp_decode sz v srcAddress dstAddress tcpLength =
  wrapDecoder sz (tCP_decoder_impl srcAddress dstAddress tcpLength) v

(** val fiat_udp_encode :
    OCamlNativeInt.t -> uDP_Packet -> CstructBytestring.storage_t ->
    CstructBytestring.storage_t -> Int64Word.t -> CstructBytestring.storage_t
    -> CstructBytestring.storage_t option **)

let fiat_udp_encode sz v srcAddress dstAddress udpLength =
  wrapEncoder sz (fun sz0 v0 pkt ->
    uDP_encoder_impl srcAddress dstAddress udpLength pkt sz0 v0) v

(** val fiat_udp_decode :
    OCamlNativeInt.t -> CstructBytestring.storage_t -> Int64Word.t
    StackVector.t -> Int64Word.t StackVector.t -> Int64Word.t -> uDP_Packet
    option **)

let fiat_udp_decode sz v srcAddress dstAddress udpLength =
  wrapDecoder sz (uDP_decoder_impl srcAddress dstAddress udpLength) v

type fiat_ethernet_type =
| ARP
| IP
| IPV6
| RARP

(** val fiat_ethernet_type_of_enum :
    char list enumType -> fiat_ethernet_type **)

let fiat_ethernet_type_of_enum enum =
  injectEnum (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))) (StackVector.cons (ARP, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (StackVector.cons (IP,
    (Pervasives.succ (Pervasives.succ 0)), (StackVector.cons (IPV6,
    (Pervasives.succ 0), (StackVector.cons (RARP, 0,
    StackVector.empty ())))))))) enum

(** val fiat_ethernet_type_to_enum :
    fiat_ethernet_type -> char list enumType **)

let fiat_ethernet_type_to_enum = function
| ARP ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))) (StackVector.cons (('A'::('R'::('P'::[]))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (StackVector.cons (('I'::('P'::[])), (Pervasives.succ (Pervasives.succ
    0)), (StackVector.cons (('I'::('P'::('V'::('6'::[])))), (Pervasives.succ
    0), (StackVector.cons (('R'::('A'::('R'::('P'::[])))), 0,
    StackVector.empty ())))))))) { bindex = ('A'::('R'::('P'::[]))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))) 0 (ArrayVector.zero (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) }
| IP ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))) (StackVector.cons (('A'::('R'::('P'::[]))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (StackVector.cons (('I'::('P'::[])), (Pervasives.succ (Pervasives.succ
    0)), (StackVector.cons (('I'::('P'::('V'::('6'::[])))), (Pervasives.succ
    0), (StackVector.cons (('R'::('A'::('R'::('P'::[])))), 0,
    StackVector.empty ())))))))) { bindex = ('I'::('P'::[])); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))) (Pervasives.succ 0) (ArrayVector.zero (Pervasives.succ
      (Pervasives.succ 0)))) }
| IPV6 ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))) (StackVector.cons (('A'::('R'::('P'::[]))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (StackVector.cons (('I'::('P'::[])), (Pervasives.succ (Pervasives.succ
    0)), (StackVector.cons (('I'::('P'::('V'::('6'::[])))), (Pervasives.succ
    0), (StackVector.cons (('R'::('A'::('R'::('P'::[])))), 0,
    StackVector.empty ())))))))) { bindex = ('I'::('P'::('V'::('6'::[]))));
    indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ 0))
      (Pervasives.succ (Pervasives.succ 0)) (ArrayVector.zero
      (Pervasives.succ 0))) }
| RARP ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))) (StackVector.cons (('A'::('R'::('P'::[]))),
    (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))),
    (StackVector.cons (('I'::('P'::[])), (Pervasives.succ (Pervasives.succ
    0)), (StackVector.cons (('I'::('P'::('V'::('6'::[])))), (Pervasives.succ
    0), (StackVector.cons (('R'::('A'::('R'::('P'::[])))), 0,
    StackVector.empty ())))))))) { bindex = ('R'::('A'::('R'::('P'::[]))));
    indexb =
    ((fun _ n p -> n + p) (Pervasives.succ 0) (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))) (ArrayVector.zero 0)) }

type fiat_arp_hardtype =
| Ethernet
| IEEE802
| Chaos

(** val fiat_arp_hardtype_of_enum :
    char list enumType -> fiat_arp_hardtype **)

let fiat_arp_hardtype_of_enum enum =
  injectEnum (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
    (StackVector.cons (Ethernet, (Pervasives.succ (Pervasives.succ 0)),
    (StackVector.cons (IEEE802, (Pervasives.succ 0), (StackVector.cons
    (Chaos, 0, StackVector.empty ())))))) enum

(** val fiat_arp_hardtype_to_enum :
    fiat_arp_hardtype -> char list enumType **)

let fiat_arp_hardtype_to_enum = function
| Ethernet ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ 0))
    (StackVector.cons
    (('E'::('t'::('h'::('e'::('r'::('n'::('e'::('t'::[])))))))),
    (Pervasives.succ (Pervasives.succ 0)), (StackVector.cons
    (('I'::('E'::('E'::('E'::('8'::('0'::('2'::[]))))))), (Pervasives.succ
    0), (StackVector.cons (('C'::('h'::('a'::('o'::('s'::[]))))), 0,
    StackVector.empty ())))))) { bindex =
    ('E'::('t'::('h'::('e'::('r'::('n'::('e'::('t'::[])))))))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))) 0 (ArrayVector.zero (Pervasives.succ (Pervasives.succ 0)))) }
| IEEE802 ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ 0))
    (StackVector.cons
    (('E'::('t'::('h'::('e'::('r'::('n'::('e'::('t'::[])))))))),
    (Pervasives.succ (Pervasives.succ 0)), (StackVector.cons
    (('I'::('E'::('E'::('E'::('8'::('0'::('2'::[]))))))), (Pervasives.succ
    0), (StackVector.cons (('C'::('h'::('a'::('o'::('s'::[]))))), 0,
    StackVector.empty ())))))) { bindex =
    ('I'::('E'::('E'::('E'::('8'::('0'::('2'::[]))))))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ 0))
      (Pervasives.succ 0) (ArrayVector.zero (Pervasives.succ 0))) }
| Chaos ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ 0))
    (StackVector.cons
    (('E'::('t'::('h'::('e'::('r'::('n'::('e'::('t'::[])))))))),
    (Pervasives.succ (Pervasives.succ 0)), (StackVector.cons
    (('I'::('E'::('E'::('E'::('8'::('0'::('2'::[]))))))), (Pervasives.succ
    0), (StackVector.cons (('C'::('h'::('a'::('o'::('s'::[]))))), 0,
    StackVector.empty ())))))) { bindex =
    ('C'::('h'::('a'::('o'::('s'::[]))))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ 0) (Pervasives.succ
      (Pervasives.succ 0)) (ArrayVector.zero 0)) }

type fiat_arp_prottype =
| IPv4
| IPv6

(** val fiat_arp_prottype_of_enum :
    char list enumType -> fiat_arp_prottype **)

let fiat_arp_prottype_of_enum enum =
  injectEnum (Pervasives.succ (Pervasives.succ 0)) (StackVector.cons (IPv4,
    (Pervasives.succ 0), (StackVector.cons (IPv6, 0, StackVector.empty ()))))
    enum

(** val fiat_arp_prottype_to_enum :
    fiat_arp_prottype -> char list enumType **)

let fiat_arp_prottype_to_enum = function
| IPv4 ->
  boundedIndex_inj_EnumType (Pervasives.succ 0) (StackVector.cons
    (('I'::('P'::('v'::('4'::[])))), (Pervasives.succ 0), (StackVector.cons
    (('I'::('P'::('v'::('6'::[])))), 0, StackVector.empty ())))) { bindex =
    ('I'::('P'::('v'::('4'::[])))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ 0)) 0
      (ArrayVector.zero (Pervasives.succ 0))) }
| IPv6 ->
  boundedIndex_inj_EnumType (Pervasives.succ 0) (StackVector.cons
    (('I'::('P'::('v'::('4'::[])))), (Pervasives.succ 0), (StackVector.cons
    (('I'::('P'::('v'::('6'::[])))), 0, StackVector.empty ())))) { bindex =
    ('I'::('P'::('v'::('6'::[])))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ 0) (Pervasives.succ 0)
      (ArrayVector.zero 0)) }

type fiat_arp_operation =
| Request
| Reply
| RARPRequest
| RARPReply

(** val fiat_arp_operation_of_enum :
    char list enumType -> fiat_arp_operation **)

let fiat_arp_operation_of_enum enum =
  injectEnum (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))) (StackVector.cons (Request, (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (StackVector.cons (Reply,
    (Pervasives.succ (Pervasives.succ 0)), (StackVector.cons (RARPRequest,
    (Pervasives.succ 0), (StackVector.cons (RARPReply, 0,
    StackVector.empty ())))))))) enum

(** val fiat_arp_operation_to_enum :
    fiat_arp_operation -> char list enumType **)

let fiat_arp_operation_to_enum = function
| Request ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))) (StackVector.cons
    (('R'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))), (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (StackVector.cons
    (('R'::('e'::('p'::('l'::('y'::[]))))), (Pervasives.succ (Pervasives.succ
    0)), (StackVector.cons
    (('R'::('A'::('R'::('P'::('R'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))),
    (Pervasives.succ 0), (StackVector.cons
    (('R'::('A'::('R'::('P'::('R'::('e'::('p'::('l'::('y'::[]))))))))), 0,
    StackVector.empty ())))))))) { bindex =
    ('R'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))) 0 (ArrayVector.zero (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))) }
| Reply ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))) (StackVector.cons
    (('R'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))), (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (StackVector.cons
    (('R'::('e'::('p'::('l'::('y'::[]))))), (Pervasives.succ (Pervasives.succ
    0)), (StackVector.cons
    (('R'::('A'::('R'::('P'::('R'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))),
    (Pervasives.succ 0), (StackVector.cons
    (('R'::('A'::('R'::('P'::('R'::('e'::('p'::('l'::('y'::[]))))))))), 0,
    StackVector.empty ())))))))) { bindex =
    ('R'::('e'::('p'::('l'::('y'::[]))))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))) (Pervasives.succ 0) (ArrayVector.zero (Pervasives.succ
      (Pervasives.succ 0)))) }
| RARPRequest ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))) (StackVector.cons
    (('R'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))), (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (StackVector.cons
    (('R'::('e'::('p'::('l'::('y'::[]))))), (Pervasives.succ (Pervasives.succ
    0)), (StackVector.cons
    (('R'::('A'::('R'::('P'::('R'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))),
    (Pervasives.succ 0), (StackVector.cons
    (('R'::('A'::('R'::('P'::('R'::('e'::('p'::('l'::('y'::[]))))))))), 0,
    StackVector.empty ())))))))) { bindex =
    ('R'::('A'::('R'::('P'::('R'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))))));
    indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ 0))
      (Pervasives.succ (Pervasives.succ 0)) (ArrayVector.zero
      (Pervasives.succ 0))) }
| RARPReply ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))) (StackVector.cons
    (('R'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))), (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))), (StackVector.cons
    (('R'::('e'::('p'::('l'::('y'::[]))))), (Pervasives.succ (Pervasives.succ
    0)), (StackVector.cons
    (('R'::('A'::('R'::('P'::('R'::('e'::('q'::('u'::('e'::('s'::('t'::[]))))))))))),
    (Pervasives.succ 0), (StackVector.cons
    (('R'::('A'::('R'::('P'::('R'::('e'::('p'::('l'::('y'::[]))))))))), 0,
    StackVector.empty ())))))))) { bindex =
    ('R'::('A'::('R'::('P'::('R'::('e'::('p'::('l'::('y'::[])))))))));
    indexb =
    ((fun _ n p -> n + p) (Pervasives.succ 0) (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))) (ArrayVector.zero 0)) }

type fiat_ipv4_protocol =
| ICMP
| TCP
| UDP

(** val fiat_ipv4_protocol_of_enum :
    char list enumType -> fiat_ipv4_protocol **)

let fiat_ipv4_protocol_of_enum proto =
  injectEnum (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
    (StackVector.cons (ICMP, (Pervasives.succ (Pervasives.succ 0)),
    (StackVector.cons (TCP, (Pervasives.succ 0), (StackVector.cons (UDP, 0,
    StackVector.empty ())))))) proto

(** val fiat_ipv4_protocol_to_enum :
    fiat_ipv4_protocol -> char list enumType **)

let fiat_ipv4_protocol_to_enum = function
| ICMP ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ 0))
    (StackVector.cons (('I'::('C'::('M'::('P'::[])))), (Pervasives.succ
    (Pervasives.succ 0)), (StackVector.cons (('T'::('C'::('P'::[]))),
    (Pervasives.succ 0), (StackVector.cons (('U'::('D'::('P'::[]))), 0,
    StackVector.empty ())))))) { bindex = ('I'::('C'::('M'::('P'::[]))));
    indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0))) 0 (ArrayVector.zero (Pervasives.succ (Pervasives.succ 0)))) }
| TCP ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ 0))
    (StackVector.cons (('I'::('C'::('M'::('P'::[])))), (Pervasives.succ
    (Pervasives.succ 0)), (StackVector.cons (('T'::('C'::('P'::[]))),
    (Pervasives.succ 0), (StackVector.cons (('U'::('D'::('P'::[]))), 0,
    StackVector.empty ())))))) { bindex = ('T'::('C'::('P'::[]))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ (Pervasives.succ 0))
      (Pervasives.succ 0) (ArrayVector.zero (Pervasives.succ 0))) }
| UDP ->
  boundedIndex_inj_EnumType (Pervasives.succ (Pervasives.succ 0))
    (StackVector.cons (('I'::('C'::('M'::('P'::[])))), (Pervasives.succ
    (Pervasives.succ 0)), (StackVector.cons (('T'::('C'::('P'::[]))),
    (Pervasives.succ 0), (StackVector.cons (('U'::('D'::('P'::[]))), 0,
    StackVector.empty ())))))) { bindex = ('U'::('D'::('P'::[]))); indexb =
    ((fun _ n p -> n + p) (Pervasives.succ 0) (Pervasives.succ
      (Pervasives.succ 0)) (ArrayVector.zero 0)) }
