open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Bool

simple : 2 ≡ 2
simple = refl

simple2 : 2 ≡ 3 → ⊥ 
simple2 ()

cong' : {A B : Set}(f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong' f refl = refl

assAdd : (i j k : ℕ) → i + (j + k) ≡ (i + j) + k
assAdd zero j k = refl
assAdd (suc i) j k = cong suc (assAdd i j k)

commPlusZero : (j : ℕ) → j ≡ j + zero
commPlusZero zero = refl
commPlusZero (suc j) = cong suc (commPlusZero j)

commPlusSuc : (i j : ℕ) → suc (j + i) ≡ j + suc i
commPlusSuc i zero = refl
commPlusSuc i (suc j) = cong suc (commPlusSuc i j)

commPlus : (i j : ℕ) → i + j ≡ j + i
commPlus zero j = commPlusZero j
commPlus (suc i) j = trans (cong suc (commPlus i j)) (commPlusSuc i j) -- suc (j + i) ≡ j + suc i

assTimes : (i j k : ℕ) → i * (j * k) ≡ (i * j) * k
assTimes zero j k = refl
assTimes (suc i) j k = {!j!}

commTimes : (i j : ℕ) → i * j ≡ j * i 
commTimes i j = {!!}

-- commutative monoid.

distr : (i j k : ℕ) → i * (j + k) ≡ i * j + i * k
distr i j k = {!!}

-- semiring

symm : {A : Set} → (a a' : A) → a ≡ a' → a' ≡ a
symm a a' = {!a!}
--symm a .a refl = refl

