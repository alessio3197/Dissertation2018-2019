open import Data.Nat
open import Data.Product
open import Data.Fin hiding (_+_)
open import Data.Vec

-- definition that n strictly less than m → n <' m
data _<'_ : ℕ → ℕ → Set where 
     zerolt : {n : ℕ} → 0 <' suc n
     suclt : {n m : ℕ} → m <' n → suc m <' suc n

-- Gets the sum of elements of the vector
myFold : {n : ℕ} → Vec ℕ n → ℕ
myFold [] = 0
myFold (x ∷ v) = x + myFold v

--inductively gets contents of position n using Fin n to recursively iterate 
ix : {n : ℕ}{A : Set} → Fin n → Vec A n → A
ix () [] -- if vector is empty this is empty case
ix zero (x ∷ xs) = x
ix (suc f) (x ∷ xs) = ix f xs

-- auxillary to lemma, if n <' m then follows that n <' suc m
lemma2 : (n m : ℕ) → n <' m → n <' suc m
lemma2 n zero ()
lemma2 zero (suc m) s = zerolt
lemma2 (suc n) (suc m) (suclt s) = suclt (lemma2 n m s)

-- proof that if suc n is less than m, n must be less than m as well
lemma : (n m : ℕ) → suc n <' m → n <' m
lemma n zero ()
lemma n (suc m) (suclt s) = lemma2 n m s

-- Final Pigeonhole Proof
-- Vector v is n elements long where  
php : {n : ℕ} → (v :  Vec ℕ n) → n <' myFold v → (Σ (Fin n) (λ f → 1 <' ix f v)) 
php [] () -- Doesn't work if the vector is wempty
php (zero ∷ v) nlv =  suc (proj₁ ih) , proj₂ ih
    where
      ih = php v (lemma _ _ nlv)

php (suc zero ∷ v) (suclt nlv) = (suc (proj₁ ih2)) , (proj₂ ih2)
    where
      ih2 = php v nlv
      
php (suc (suc x) ∷ v) nlv = zero , (suclt zerolt)
