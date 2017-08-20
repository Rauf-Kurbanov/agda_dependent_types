module lect02 where

-- 1. Модули, open, import, hiding, renaming

open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.List renaming (length to len)

module Sort {A : Set} (_<_ : A → A → Bool) where
  sort : List A → List A
  sort xs = xs

  xx : A → A → ℕ
  xx a b = if a < b then 0 else 1

-- Просто для примера
_<<_ : ℕ → ℕ → Bool
_<<_ _ _ = false

-- open Sort _<<_

module X = Sort _<<_

open X

ff = sort []

list : List ℕ
list = 1 ∷ 2 ∷ 3 ∷ []

-- 2. Type checking

infix 3 _==_
_==_ : Bool → Bool → Bool
true == true = true
false == false = true
_ == _ = false

infixl 4 _&&_
_&&_ : Bool → Bool → Bool
-- _ && false = false
-- x && true = x
-- false && _ = false
-- true && y = y
true && true = true
_ && _ = false

foo : T (true && false == false) → ℕ
foo _ = 0

data Empty : Set where

foo' : List Empty → ℕ
foo' [] = 0
foo' (() ∷ xs)

bar = foo tt

baz : (x : Bool) → T (x && false == false)
baz false = tt
baz true = tt

-- 3. type LN = List ℕ?

LN = List ℕ

-- 4. Вселенные, полиморфизм по уровням.

-- Set : Set

-- f : Set 1 → Set 1
-- f X = X

-- f : Set₁₀₀₀₀₀₀₀₀₀₀₀ → Set₁₀₀₀₀₀₀₀₀₀₀₀
-- f X = X

data List' {l} (A : Set l) : Set l where
  nil : List' A
  cons : A → List' A → List' A

gg = cons ℕ (cons (ℕ → ℕ) nil)

-- g = f (ℕ → Set₀ → List Set₀)

h : ∀ {l} → Set l → Set l
h X = X

hh : ∀ n → T (n == n)
hh n = {!!}

g' = h Set₁

-- 5. Records.

record Point : Set where
  constructor point
  field
    x : ℕ
    y : ℕ

-- origin' = point 0 0

origin : Point
origin = record { x = 0; y = 0 }

_==''_ : ℕ → ℕ → Bool
0 =='' 0 = true
0 =='' suc y = false
suc x =='' 0 = false
suc x =='' suc y = x =='' y

_=='_ : Point → Point → Bool
point x' y' ==' q = let open Point q in x' =='' x && y' =='' y

data Point' : Set where
  point' : ℕ → ℕ → Point'

getX : Point' → ℕ
getX (point' x y) = x

getY : Point' → ℕ
getY (point' x y) = y

_=='''_ : Point' → Point' → Bool
point' x' y' ==''' point' x y = x' =='' x && y' =='' y

pfoo : (p : Point) → T (p ==' record { x = Point.x p; y = Point.y p })
pfoo p = {!!}

qfoo : (p : Point') → T (p ==''' point' (getX p) (getY p))
qfoo p = {!!}
