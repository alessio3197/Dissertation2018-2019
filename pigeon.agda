open import Data.Nat
open import Data.Product
open import Data.Fin hiding (_+_)
open import Data.Vec

module pigeon where

-- Definition that n strictly less than m → n <' m
data _<'_ : ℕ → ℕ → Set where 
     zerolt : {n : ℕ} → 0 <' suc n
     suclt : {n m : ℕ} → m <' n → suc m <' suc n

-- Gets the sum of elements of the vector
myFold : {n : ℕ} → Vec ℕ n → ℕ
myFold [] = 0
myFold (x ∷ v) = x + myFold v

-- Inductively gets contents of position n using Fin n to recursively iterate 
ix : {n : ℕ}{A : Set} → Fin n → Vec A n → A
ix () [] -- If vector is empty this is empty case
ix zero (x ∷ xs) = x
ix (suc f) (x ∷ xs) = ix f xs

-- Auxillary to lemma, if n <' m then follows that n <' suc m
lem₂ : (n m : ℕ) → n <' m → n <' suc m
lem₂ n zero ()
lem₂ zero (suc m) s = zerolt
lem₂ (suc n) (suc m) (suclt s) = suclt (lem₂ n m s)

-- Proof that if suc n is less than m, n must be less than m as well
lem : (n m : ℕ) → suc n <' m → n <' m
lem n zero ()
lem n (suc m) (suclt s) = lem₂ n m s

-- Final Pigeonhole Proof
-- Vector v is n elements long where  n is less than contents of the elements of v
-- Proof showing there exists an index Fin n where contents of element at index
-- is bigger than 1 i.e. 2 or more ∴ proving php
php : {n : ℕ} → (v :  Vec ℕ n) → n <' myFold v → (Σ (Fin n) (λ f → 1 <' ix f v)) 
php [] () -- Doesn't work if the vector is empty
php (zero ∷ v) nlv =  suc (proj₁ ih) , proj₂ ih
    where
      ih = php v (lem _ _ nlv) -- Inductive hypothesis

php (suc zero ∷ v) (suclt nlv) = suc (proj₁ ih₂) , proj₂ ih₂
    where
      ih₂ = php v nlv
      
php (suc (suc x) ∷ v) nlv = zero , suclt zerolt
