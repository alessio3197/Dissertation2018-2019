open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Fin 
open import Relation.Binary.PropositionalEquality

record Clash {n m : ℕ} (f : Fin n → Fin m) : Set where
       field
         i j : Fin n
         neq : i ≢ j
         clash : f i ≡ f j

data _<'_ : ℕ → ℕ → Set where
     zerolt : {n : ℕ} → 0 <' suc n
     suclt : {n m : ℕ} → m <' n → suc m <' suc n

insert : {n : ℕ} → (Fin n) → Fin (suc n) → Fin (suc n)
insert x zero = suc x
insert zero (suc y) = zero
insert (suc x) (suc y) = suc (insert x y)

lem : {m n : ℕ}(g : Fin n → Fin (suc m))(i : Fin (suc m)) →
          (Σ (Fin n) (λ j → g j ≡ i)) ⊎ (Σ (Fin n → Fin m) (λ f → (k : Fin n) → g k ≡ insert (f k) i))
lem g i = {!!}

open Clash

php : {m n : ℕ} → (m <' n) → (f : Fin n → Fin m) → Clash f
php zerolt f with f zero
php zerolt f | ()
php (suclt mn) f = {!!}
