module tasks03 where

open import Data.Nat hiding (_<_)
open import Data.Unit
open import Data.Product hiding(map ; zip)
open import Data.Bool

-- 1. Реализуйте аналоги функции map для vec и Vec.

vec : Set → ℕ → Set
vec A 0 = ⊤
vec A (suc n) = A × vec A n

data Vec (A : Set) : ℕ → Set where
  nil : Vec A 0
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

map : {A B : Set}{n : ℕ} -> (f : A -> B) -> (v : vec A n) -> vec B n
map {A} {B} {zero} f v = tt
map {A} {B} {suc n} f (proj₁ , proj₂) = (f proj₁) , map f proj₂

map' : {A B : Set}{n : ℕ} -> (f : A -> B) -> (v : Vec A n) -> Vec B n
map' f nil = nil
map' f (cons x xs) = cons (f x) (map' f xs)

-- 2. Реализуйте аналоги функции zipWith для vec и Vec.
--    Функция должна принимать вектора одинаковой длины.
zipWith : {A B C : Set}{n : ℕ} -> (A -> B -> C) -> (a : Vec A n) -> (b : Vec B n) -> (Vec C n)
zipWith f nil nil = nil
zipWith f (cons x a) (cons x₁ b) = cons (f x x₁) (zipWith f a b)

zipWith' : {A B C : Set}{n : ℕ} -> (A -> B -> C) -> (a : vec A n) -> (b : vec B n) -> (vec C n)
zipWith' {A} {B} {C} {zero} f a b = tt
zipWith' {A} {B} {C} {suc n} f (proj₁ , proj₂) (proj₃ , proj₄) = (f proj₁ proj₃) , (zipWith' f proj₂ proj₄)

-- 3. Функции Fin n → A соответствуют спискам элементов A длины n.
--    Функция, преобразующие Vec A n в Fin n → A была реализована на лекции.
--    Реализуйте обратную функцию.

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

coin : {A : Set} {n : ℕ} → (Fin n → A) → Vec A n
coin {A} {zero} f = nil
coin {A} {suc n} f = cons (f zero) (coin (\x -> f (suc x)))


-- 4. Определите тип матриц и ряд функций над ними.

Mat : (A : Set) → (n m : ℕ) → Set
Mat A n m = Vec (Vec A m) n

-- диагональная матрица с элементами e на диагонали и z на остальных позициях.

repeat : {A : Set} -> A -> (len : ℕ) -> Vec A len
repeat x zero = nil
repeat x (suc n) = cons x (repeat x n)

oneHot : {A : Set}(n : ℕ) (z e : A) (pos : Fin n) -> Vec A n
oneHot zero z e pos = nil
oneHot (suc n) z e zero = cons e (repeat z n)
oneHot (suc n) z e (suc pos) = cons z (oneHot n z e pos)

diag : {A : Set} → A → A → (n : ℕ) → Mat A n n
diag z e n = coin (oneHot n z e)

-- транспонирование матриц

index : {A : Set} {n : ℕ} → (k : Fin n) → Vec A n → A
index zero (cons x xs) = x
index (suc k) (cons x xs)  = index k xs

getRow : {A : Set} {n : ℕ} → Vec A n → (k : Fin n) → A
getRow M k = index k M

getColumn : {A : Set} {n m : ℕ} -> Mat A n m -> Fin m -> Vec A n
getColumn mat c = map' (index c) mat

transpose : {A : Set} {n m : ℕ} → Mat A n m → Mat A m n
transpose M = coin (getColumn M)

-- сложение матриц

add : {A : Set} (_+_ : A → A → A) → {n m : ℕ} → Mat A n m → Mat A n m → Mat A n m
add _+_ M N = coin (λ x → zipWith _+_ (getRow M x) (getRow N x))

-- умножение матриц

foldr : {A B : Set}{n : ℕ} -> (A -> B -> B) -> B -> Vec A n -> B
foldr f z nil = z
foldr f z (cons x xs) = f x (foldr f z xs)

mul : {A : Set} (z : A) (_+_ _*_ : A → A → A) → {n m k : ℕ} → Mat A n m → Mat A m k → Mat A n k
mul z _+_ _*_ M N = coin (λ i → coin (λ j → foldr _+_ z (zipWith _*_ (getRow M i) (getColumn N j))))

-- 5. Определите при помощи индуктивных семейств тип CTree A n бинарных деревьев высоты ровно n с элементами во внутренних узлах.
--    Любое такое бинарное дерево будет полным.

data CTree (A : Set) : ℕ → Set where
  leaf : CTree A 0
  node : {n : ℕ} -> A -> (CTree A n) -> (CTree A n) -> (CTree A (suc n))

-- 6. Определите при помощи индуктивных семейств тип Tree A n бинарных деревьев высоты не больше n с элементами во внутренних узлах.

_<_ : ℕ -> ℕ -> Bool
zero < zero = false
zero < _ = true
_ < zero = false
(suc n) < (suc m) = n < m


-- data Tree (A : Set) : ℕ → Set where
  -- leaf  : Tree A 0
  -- left  : {n m : ℕ} →  T(m < n) → A -> (Tree A n) -> (Tree A m) → Tree A (suc n)
  -- right : {n m : ℕ} →  T(not (m < n)) → A -> (Tree A n) -> (Tree A m) → Tree A (suc m)

-- -- определите функцию, возвращающую высоту дерева.

-- height : {A : Set} (n : ℕ) → Tree A n → Fin (suc n)
-- height zero leaf = zero
-- height (suc n) (left x x₁ tree tree₁) = suc (height n tree)
-- height (suc n) (right x x₁ tree tree₁) = suc (height n tree₁)

data Tree (A : Set) : ℕ → Set where
  leaf : {n : ℕ} -> Tree A n
  node : {n : ℕ} -> A -> (Tree A n) -> (Tree A n) -> (Tree A (suc n))

height : {A : Set} (n : ℕ) → Tree A n → Fin (suc n)
height zero tree = zero
height (suc n) leaf = zero
height (suc n) (node x tree tree₁) = {!   !}
