module task02 where

-- 1.
data Bool : Set where
    true false : Bool

infix 7 _||_
_||_ : Bool → Bool → Bool
true || _ = true
false || x = x

infix 8 _and_
_and_ : Bool → Bool → Bool
true and x = x
false and _ = false

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

infix 3 _=='_
_=='_ : ℕ → ℕ → Bool
zero ==' zero = true
zero ==' suc _ = false
suc _ ==' zero = false
suc x ==' suc y = x ==' y

_===_ : List ℕ → List ℕ → Bool
nil === nil = true
nil === _ = false
_ === nil = false
cons x xs === cons y ys = (x ==' y) and (xs === ys)

data Unit : Set where
  unit : Unit

data Empty : Set where

T : Bool → Set
T true = Unit
T false = Empty

reverse' : {A : Set} → List A → List A → List A
reverse' acc nil = acc
reverse' acc (cons x xs) = reverse' (cons x acc) xs

reverse : {A : Set} → List A → List A
reverse = reverse' nil

reflN : (n : ℕ) → T (n ==' n)
reflN zero = unit
reflN (suc n) = reflN n

and-lem : (x y : Bool) -> T x -> T y -> T (x and y)
and-lem true true p q = unit
and-lem true false p ()
and-lem false true () q
and-lem false false () q

refl : (xs : List ℕ) → T (xs === xs)
refl nil = unit
refl (cons x xs) = and-lem _ _ (reflN x) (refl xs)

reverse'-invol : (ys xs : List ℕ) → T (reverse (reverse' ys xs) === reverse' xs ys)
reverse'-invol ys nil = refl (reverse ys)
reverse'-invol ys (cons x xs) = reverse'-invol (cons x ys) xs

reverse-invol : (xs : List ℕ) → T (reverse (reverse' nil xs) === reverse' xs nil)
reverse-invol = reverse'-invol nil

open import Data.Unit

record Point {l} (A B : Set l) : Set l where
    constructor point
    field
      a : A
      b : B

-- 3.
_<_ : ℕ → ℕ → Bool
_ < zero = false
zero < suc y = true
suc x < suc y = x < y

length : {A : Set} → List A → ℕ
length nil = zero
length (cons x xs) = suc (length xs)

lookUp : {A : Set}(ll : List A)(n : ℕ) → T (n < length ll) → A
lookUp nil n ()
lookUp (cons x xs) zero p = x
lookUp (cons x xs) (suc n) p = lookUp xs n p
