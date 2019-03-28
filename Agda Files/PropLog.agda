open import Data.Product 
open import Data.Sum 
open import Data.Unit 
open import Data.Empty 

{- Propositional logic -}

Prp : Set₁
Prp = Set

infix 3 _∧_
_∧_ : Prp → Prp → Prp -- and
P ∧ Q = P × Q

infix 2 _∨_
_∨_ : Prp → Prp → Prp -- or
P ∨ Q = P ⊎ Q

True : Prp
True = ⊤

False : Prp
False = ⊥

efq : {P : Prp} → False → P -- ex falso quod libet
efq ()

¬ : Prp → Prp
¬ P = P → False

infix 1 _↔_
_↔_ : Prp → Prp → Prp
P ↔ Q = (P → Q) ∧ (Q → P)
