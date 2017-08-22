module tasks04 where

open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Data.Sum
open import Data.Vec hiding (reverse) renaming (_++_ to _+V+_)
open import Data.List hiding (reverse) renaming (_++_ to _+L+_)
open import Relation.Binary.PropositionalEquality hiding (sym; trans; cong; cong₂)
open import Data.Unit
open import Data.Bool

-- 2. Определите симметричность, транзитивность и конгруэнтность при помощи паттерн матчинга.

sym : {A : Set} {a a' : A} → a ≡ a' → a' ≡ a
sym refl = refl

trans : {A : Set} {a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl refl = refl

cong : {A B : Set} (f : A → B) {a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

-- 3. Определите конгруэнтность для функций двух аргументов через subst.

cong₂ : {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ f {a} {a'} {b} {b'} p q = subst (λ x → f a b ≡ f a' x) q (subst (λ x → f a b ≡ f x b) p refl)

-- 1. Доказать следующий факт.

fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = suc n * fac n

_==_ : (ℕ → ℕ) → (ℕ → ℕ) → Set
f == g = (x : ℕ) → f x ≡ g x

D : ℕ → Set
D zero = ⊥
D (suc _) = ⊤

infix 1 _=='_
_=='_ : ℕ → ℕ → Bool
0 ==' 0 = true
0 ==' suc _ = false
suc _ ==' 0 = false
suc x ==' suc y = x ==' y

≡-== : {x y : ℕ} → x ≡ y → T (x ==' y)
≡-== {zero} {zero} p = tt
≡-== {zero} {suc y} ()
≡-== {suc x} {zero} p = subst D p tt
≡-== {suc x} {suc y} p = ≡-== (cong pred p)

lem : fac == suc → ⊥
lem p = ≡-== (p 3)

-- 4. Докажите дистрибутивность умножения над сложением для натуральных чисел.

open ≡-Reasoning

+-assoc : (x : ℕ) {y z : ℕ} → (x + y) + z ≡ x + (y + z)
+-assoc zero = refl
+-assoc (suc x) = cong suc (+-assoc x)

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm zero y)
+-comm (suc x) zero = cong suc (+-comm x zero)
+-comm (suc x) (suc y) = cong suc (trans (+-comm x (suc y)) (trans (cong suc (sym (+-comm x y))) (+-comm (suc x) y)))

distr : (n m k : ℕ) → n * (m + k) ≡ n * m + n * k
distr zero m k = refl
distr (suc n) m k =
  (begin
    (suc n) * (m + k)
  ≡⟨ cong (λ x → (m + k) + x) (distr n m k) ⟩
    (m + k) + (n * m + n * k)
  ≡⟨ +-assoc m ⟩
    m + (k + (n * m + n * k))
  ≡⟨ cong (λ x → m + x) (+-comm k (n * m + n * k)) ⟩
    m + ((n * m + n * k) + k)
  ≡⟨ cong (λ x → m + x) (+-assoc (n * m)) ⟩
    m + (n * m + (n * k + k))
  ≡⟨ cong (λ x → m + x) (+-comm (n * m)  (n * k + k)) ⟩
    m + ((n * k + k) + n * m)
  ≡⟨ +-comm m ((n * k + k) + n * m) ⟩
    ((n * k + k) + n * m) + m
  ≡⟨ +-assoc (n * k + k) ⟩
    (n * k + k) + (n * m + m)
  ≡⟨ cong (λ x → x + (n * m + m)) (+-comm (n * k) k) ⟩
    (k + n * k) + (n * m + m)
  ≡⟨ cong (λ x → (k + n * k) + x) (+-comm (n * m) m) ⟩
    (k + n * k) + (m + n * m)
  ≡⟨ +-comm (k + n * k) (m + n * m) ⟩
    (m + n * m) + (k + n * k)
  ∎)

-- 7. Докажите, что [] является нейтральным элементом для ++.

[]-is-neutral : {A : Set} {n : ℕ} (xs : Vec A n) → subst (Vec A) (+-comm n 0) (xs +V+ []) ≡ xs
[]-is-neutral [] = refl
[]-is-neutral (x ∷ xs) =
  {! begin
      reverse (xs +L+ [])   
    ≡⟨ cong reverse {! []-is-neutral ? ? ?  !} ⟩
      (reverse xs)
      ∎  !}

-- 6. Докажите следующее утверждение.

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs +L+ x ∷ []

reverse-append : {A : Set} (xs ys : List A) → reverse (xs +L+ ys) ≡ reverse ys +L+ reverse xs
reverse-append [] [] = refl
reverse-append [] ys =
  begin
    reverse ([] +L+ ys)
  ≡⟨ cong reverse {!   !} ⟩
    reverse ys
  ≡⟨ {! !} ⟩
    (reverse ys +L+ [])
  ≡⟨ {!   !} ⟩
    (reverse ys +L+ reverse [])
   ∎
reverse-append xs [] =
  begin
    reverse (xs +L+ [])
  ≡⟨ cong reverse {! []-is-neutral ? ? ?  !} ⟩
    (reverse xs)
    ∎
reverse-append (x ∷ xs) (x₁ ∷ ys) = {!   !}

-- 5. Докажите следующее утверждение.

reverse-inv : {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-inv [] = refl
reverse-inv (x ∷ xs) = begin
    reverse (reverse (xs) +L+ x ∷ [])
  ≡⟨ reverse-append (reverse xs) (x ∷ []) ⟩
    x ∷ (reverse (reverse xs))
  ≡⟨ cong (λ y → x ∷ y) (reverse-inv xs) ⟩
    (x ∷ xs)
  ∎

-- 8. Определите reverse для Vec через аккумулятор.

rev-helper : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
rev-helper {A} {n = n} acc [] = subst (Vec A) (+-comm 0 n) acc
rev-helper {A} {n} {suc m} acc (x ∷ xs) = subst (Vec A)
  (begin
    suc (n + m)
  ≡⟨ cong suc (+-comm n m) ⟩
    suc (m + n)
  ≡⟨ +-comm (suc m) n ⟩
    n + suc m
  ∎)
  (rev-helper (x ∷ acc) xs)

rev : {A : Set} {n : ℕ} → Vec A n → Vec A n
rev = rev-helper []

-- 9. Докажите, что [] не равно x ∷ xs при помощи паттер матчинга.

List-diff : {A : Set} (x : A) (xs : List A) → _≡_ {A = List A} [] (x ∷ xs) → ⊥
List-diff _ _ ()

-- 10. Докажите, что [] не равно x ∷ xs при помощи subst.

f : {A : Set}(xs : List A) -> Set
f [] = ⊤
f (x ∷ xs) = ⊥

List-diff' : {A : Set} (x : A) (xs : List A) → _≡_ {A = List A} [] (x ∷ xs) → ⊥
List-diff' _ _ p = subst f p tt
