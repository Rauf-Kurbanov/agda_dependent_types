module tasks01 where

-- 0. Определить flip, const
flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

const : {A B : Set} → A → B → A
const x y = x

-- 1. Определить миксфикссный if_then_else_ полиморфный по возвращаемому значению

data Bool : Set where
    true false : Bool

not : Bool → Bool
not true = false
not false = true

infix 7 _||_
_||_ : Bool → Bool → Bool
true || _ = true
false || x = x

infix 8 _and_
_and_ : Bool → Bool → Bool
true and x = x
false and _ = false

if_then_else_ : {A : Set} → Bool → A → A → A
if_then_else_ true t _ = t
if_then_else_ false _ f = f

-- 2. Определить возведение в степень и факториал для натуральных чисел

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

infix 5 _+_
_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

infix 6 _*_
_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + x * y

_^_ : ℕ → ℕ → ℕ
_^_ x zero = suc zero
_^_ x (suc y) = x * (x ^ y)

fac : ℕ → ℕ
fac zero  = suc zero
fac (suc n) = (suc n) * fac n

-- 3. Определите mod и gcd

_-_ : ℕ → ℕ → ℕ
zero - y = zero
suc x - zero = suc x
suc x - suc y = x - y

_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y

div' : ℕ → ℕ → ℕ → ℕ
div' zero x y = zero
div' (suc c) x y = if (x < y) then zero else suc (div' c (x - y) y)

div : ℕ → ℕ → ℕ
div x y = div' x x y

mod : ℕ → ℕ → ℕ
mod x y = (div x y) * y - x

gcd' : ℕ → ℕ → ℕ → ℕ
gcd' zero a b = a
gcd' _ zero b = b
gcd' _ a zero = a
gcd' (suc c) a b  =  if a < b then gcd' c a (mod b a) else gcd' c (mod a b) b

max : ℕ → ℕ → ℕ
max a b = if a < b then b else a

gcd : ℕ → ℕ → ℕ
gcd a b = gcd' (max a b) a b

-- 4. Определить (полиморфный) reverse для списков

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
nil ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)

reverse' : {A : Set} → List A → List A → List A
reverse' nil acc = acc
reverse' (cons x xs) acc = reverse' xs (cons x acc)

reverse : {A : Set} → List A → List A
reverse = reverse' nil

-- 5. Реализовать любой алгоритм сортировки

filter : {A : Set} → (A -> Bool) → List A → List A
filter _ nil = nil
filter pred (cons x xs) = if (pred x) then (cons x (filter pred xs)) else filter pred xs

sort : List ℕ → List ℕ
sort nil = nil
sort (cons x xs) = lt ++ (cons x gte)
  where
    lt = filter (\a → a < x) (cons x xs)
    gte = filter (\a → not (a < x)) (cons x xs)


-- 6. Докажите ассоциативность ||

data Unit : Set where
  unit : Unit

data Empty : Set where

absurd : {A : Set} → Empty → A
absurd ()

T : Bool → Set
T true = Unit
T false = Empty

infix 3 _==_
_==_ : Bool → Bool → Bool
true == true = true
true == false = false
false == true = false
false == false = true

||-assoc : (x y z : Bool) → T ((x || y) || z == x || (y || z))
||-assoc false false false = unit
||-assoc false false true = unit
||-assoc false true false = unit
||-assoc false true true = unit
||-assoc true false false = unit
||-assoc true false true = unit
||-assoc true true false = unit
||-assoc true true true = unit

-- 7. Докажите, что fac 3 равен 6 и что fac 2 не равен 3.

infix 3 _=='_
_=='_ : ℕ → ℕ → Bool
zero ==' zero = true
zero ==' suc _ = false
suc _ ==' zero = false
suc x ==' suc y = x ==' y

gcd-check : T ((gcd (suc (suc (suc (suc zero)))) (suc (suc zero))) ==' (suc (suc zero)))
gcd-check = unit

fac3=6 : T (fac (suc (suc (suc zero))) ==' suc (suc (suc (suc (suc (suc zero))))))
fac3=6 = unit

fac2≠3 : T (fac (suc (suc zero)) ==' suc (suc (suc zero))) → Empty
fac2≠3 ()

-- 8. Определите равенство для списков натуральных чисел; докажите, что для любого xs : List ℕ верно, что reverse (reverse xs) равно xs
_===_ : List ℕ → List ℕ → Bool
nil === nil = true
nil === _ = false
_ === nil = false
cons x xs === cons y ys = (x ==' y) and (xs === ys)

data _==_ 
-- reverse-invol : (xs : List ℕ) → T (reverse (reverse nil) === nil)
-- reverse-invol nil = unit
-- reverse-invol (cons x xs) = reverse-invol xs
