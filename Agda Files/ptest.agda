open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Fin 
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Bool hiding (_∨_)
open import Data.Maybe
open import PropLog


record Clash {n m : ℕ} (f : Fin n → Fin m) : Set where
       field
         i j : Fin n
         clash : f i ≡ f j

_<'_ : ℕ → ℕ → Bool
n <' zero = false
zero <' suc m = true
suc n <' suc m = n <' m

_<'f_ : {n m : ℕ} → (x : Fin n) → (y : Fin m) → Bool
x <'f y = toℕ x <' toℕ y

insert : {n : ℕ} → (Fin n) → Fin (suc n) → Fin (suc n)
insert x zero = suc x
insert zero (suc y) = zero
insert (suc x) (suc y) = suc (insert x y)

open Clash

pid : (n m : ℕ) → T (m <' n) → (f : Fin (suc n) → Fin (suc m)) → Clash f
pid zero zero () f
pid (suc n) zero p f = {!!}
pid zero (suc n') () f
pid (suc n) (suc m) mln f = {!!}

php : (n m : ℕ) → T (m <' n) → (f : Fin n → Fin m) → Clash f
php zero m () f
php (suc n) zero mln f with f zero
php (suc n) zero mln f | ()
php (suc n) (suc m) mln f = ?

