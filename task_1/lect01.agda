module lect01 where

-- 1. Bool, not, ||, if then else

-- 2. Nat, +, *

-- 3. Termination, gcd

{-
_-_ : ℕ → ℕ → ℕ
zero - y = zero
suc x - zero = suc x
suc x - suc y = x - y

_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y

div : ℕ → ℕ → ℕ
div x y = if (x < y) then zero else suc (div (x - y) y)
-}

-- 4. Полиморфизм, id, неявные аргументы

-- 5. Списки, append

-- 6. Пустой и одноэлементный типы

-- 7. Пример утверждений и доказательств, not (not x) == x
