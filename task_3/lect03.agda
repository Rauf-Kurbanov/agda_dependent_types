module lect03 where

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.Bool

-- 1. Определить Vec рекурсивно.

-- List : Set → Set

vec : Set → ℕ → Set
-- vec A n
vec A 0 = ⊤
vec A (suc n) = A × vec A n

list'' : vec ℕ 0
list'' = tt

list : vec ℕ 3
list = 0 , 1 , 2 , tt

head' : {A : Set} {n : ℕ} → vec A (suc n) → A
head' (x , _) = x

tail' : {A : Set} {n : ℕ} → vec A (suc n) → vec A n
tail' (_ , xs) = xs

-- 2. Определить Vec индуктивно.

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

_==_ : ℕ → ℕ → Bool
0 == 0 = true
0 == suc _ = false
suc _ == 0 = false
suc n == suc k = n == k

data Vec₂ (A : Set) (n : ℕ) : Set where
  nil : T (n == 0) → Vec₂ A n
  cons : {n' : ℕ} → T (n == suc n') → A → Vec₂ A n' → Vec₂ A n

-- vec : Set → ℕ → Set
-- Vec : Set → ℕ → Set

data Vec (A : Set) : ℕ → Set where
  nil : Vec A 0
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

list₀ : Vec ℕ 0
list₀ = nil

list₁ : Vec ℕ 1
list₁ = cons 10 nil

list₂ : Vec ℕ 2
list₂ = cons 300 (cons 321 nil)

-- 3. Определить head, tail и append.

-- foo : Vec ℕ 0 → ℕ
-- foo nil = 3

head : {A : Set} {n : ℕ} → Vec A (suc n) → A
head (cons x _) = x

tail : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A n
tail (cons _ xs) = xs

-- 4. Определить функцию length для Vec.

length : {A : Set} → List A → ℕ
length nil = 0
length (cons x xs) = 1 + length xs

len : {A : Set} {n : ℕ} → Vec A n → ℕ
len nil = 0
len (cons _ xs) = 1 + len xs

-- 5. Обсудить dot паттерны.

_++_ : {A : Set} {n k : ℕ} → Vec A n → Vec A k → Vec A (n + k)
nil ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)

data Vec₃ (A : Set) : ℕ → Set where
  nil : Vec₃ A 0
  cons : (n : ℕ) → A → Vec₃ A n → Vec₃ A (suc n)

head₃ : {A : Set} (n : ℕ) → Vec₃ A (suc n) → A
head₃ n (cons .n x _) = x

tail₃ : {A : Set} {n : ℕ} → Vec₃ A (suc n) → Vec₃ A n
tail₃ (cons n _ xs) = xs

fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = suc n * fac n

tail-fac : {A : Set} (n : ℕ) → Vec A (suc (fac n)) → Vec A (fac n)
tail-fac n (cons x xs) = xs

----------------------------------------------------

-- Bad!!!
-- data Foo : ℕ → Set where
--   foo : (n : ℕ) → Foo (fac n)

-- Good!!!
data Foo (k : ℕ) : Set where
  foo : (n : ℕ) → T (k == fac n) → Foo k

baz : (n k : ℕ) → Foo (n + k) → ℕ
baz n k (foo n₁ x) = zero

----------------------------------------------------

data Bar (A : Set) : A → A → Set where
  bar : (n : A) → Bar A n n

-- 7. Fin, toℕ, index

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

zero₁ : Fin 1
zero₁ = zero

-- one₁ : Fin 1
-- one₁ = suc zero

-- zero : Fin 2
-- suc zero : Fin 2

-- zero : Fin 3
-- suc zero : Fin 3
-- suc (suc zero) : Fin 3

index : {A : Set} {n : ℕ} → Vec A n → (k : Fin n) → A
index (cons x xs) zero = x
index (cons x xs) (suc k) = index xs k

toℕ : {n : ℕ} → Fin n → ℕ
toℕ zero = zero
toℕ (suc x) = suc (toℕ x)
