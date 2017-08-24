module tasks05 where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty

-- 1. Используя тип List, определите тип данных (через зависимые записи) списков длины n (число должно быть параметром записи).
--    Реализуйте для такого типа функции head и tail.

record ListN (A : Set)(n : ℕ) : Set where
  constructor listN
  field
    list : List A
    proof : length list ≡ n

head : {A : Set}{n : ℕ} -> ListN A (suc n) -> A
head (listN [] ())
head (listN (x ∷ list) refl) = x

tail : {A : Set}{n : ℕ} -> ListN A (suc n) -> ListN A n
tail (listN [] ())
tail (listN (x ∷ list) proof) = listN list (cong pred proof)

-- 2. Определите тип (через зависимые записи) четных натуральных чисел.
--    Определите функцию деления на 2.

isEven : (n : ℕ) -> Set
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n

record Evenℕ : Set where
  constructor evenN
  field
    n : ℕ
    proof : isEven n

div2 : Evenℕ → ℕ
div2 (evenN zero tt) = zero
div2 (evenN (suc zero) ())
div2 (evenN (suc (suc n)) proof) = 1 + div2 (evenN n proof)

-- 3. Постройте структуру моноида на типе натуральных чисел (т.е. нужно сконструировать элемент соответствующей записи).

+-assoc : (x : ℕ) {y z : ℕ} → (x + y) + z ≡ x + (y + z)
+-assoc zero = refl
+-assoc (suc x) = cong suc (+-assoc x)

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm zero zero = refl
+-comm zero (suc y) = cong suc (+-comm zero y)
+-comm (suc x) zero = cong suc (+-comm x zero)
+-comm (suc x) (suc y) = cong suc (trans (+-comm x (suc y))
  (trans (cong suc (+-comm y x)) (+-comm (suc x) y)))

record Monoid : Set₁ where
  field
    A : Set
    id : A
    _#_ : A → A → A
    assoc : (x y z : A) → (x # y) # z ≡ x # (y # z)
    id-left : (x : A) → id # x ≡ x
    id-right : (x : A) → x # id ≡ x

ℕ-Monoid : Monoid
ℕ-Monoid = record {
  A = ℕ;
  id = 0;
  _#_ = _+_;
  assoc = λ x _ _ → +-assoc x ;
  id-left = λ x → refl;
  id-right = λ x → trans (+-comm x 0) refl }

-- 4. Напишите тип монады (через зависимые записи).
--    Элементы этого типа должны удовлетворять всем законом монад.

record Monad (M : Set → Set) : Set₁ where
  field
    _>>=_ : {A B : Set} -> M A -> (A -> M B) -> (M B)
    _>>_ : {A B : Set} -> M A -> M B -> M B
    return : {A : Set} -> A -> M A
    left-id : {A B : Set}{f : A -> M B}{a : A} -> return a >>= f ≡ f a
    right-id : {A : Set}{a : M A} -> a >>= return ≡ a
    assoc : {A B C : Set}{m : M A}{f : A -> M B}{g : B -> M C} -> (m >>= f) >>= g ≡ m >>= (λ x -> f x >>= g)

-- 5. Определите тип данных Maybe, сконструируйте структуру функтора и монады на этом типе.

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set} (a : F A) → fmap (λ x → x) a ≡ a
    fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : F A) → fmap (λ x → g (f x)) a ≡ fmap g (fmap f a)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

maybe-fmap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
maybe-fmap f nothing = nothing
maybe-fmap f (just x) = just (f x)

maybe-fmap-id : {A : Set} (a : Maybe A) → maybe-fmap (λ x → x) a ≡ a
maybe-fmap-id nothing = refl
maybe-fmap-id (just x) = refl

maybe-fmap-comp : {A B C : Set} (f : A → B) (g : B → C) (a : Maybe A) →
 maybe-fmap (λ x → g (f x)) a ≡ maybe-fmap g (maybe-fmap f a)
maybe-fmap-comp f g nothing = refl
maybe-fmap-comp f g (just x) = refl

Maybe-Functor : Functor Maybe
Maybe-Functor = record { fmap = maybe-fmap; fmap-id = maybe-fmap-id; fmap-comp = maybe-fmap-comp }

_m>>=_ : {A B : Set} -> Maybe A -> (A -> Maybe B) -> (Maybe B)
_m>>=_ nothing f = nothing
_m>>=_ (just x) f = f x

_m>>_ : {A B : Set} -> Maybe A -> Maybe B -> Maybe B
_m>>_ m n = n

proof : {A : Set}{a : Maybe A} -> a m>>= just ≡ a
proof {A} {nothing} = refl
proof {A} {just x} = refl

massoc : {A B C : Set}{m : Maybe A}{f : A -> Maybe B}{g : B -> Maybe C} -> (m m>>= f) m>>= g ≡ m m>>= (λ x -> f x m>>= g)
massoc {A} {B} {C} {nothing} {f} {g} = refl
massoc {A} {B} {C} {just x} {f} {g} = refl

Maybe-Monad : Monad Maybe
Maybe-Monad = record {
  _>>=_ = _m>>=_;
  _>>_ = _m>>_;
  return = just;
  left-id = λ {A} {B} {f} {a} → refl;
  right-id = λ {A} {a} → proof;
  assoc = λ {A} {B} {C} {m} {f} {g} → massoc {A} {B} {C} {m} {f} {g}}
