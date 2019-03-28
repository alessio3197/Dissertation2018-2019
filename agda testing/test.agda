module test where

data Bool : Set where
     true : Bool
     false : Bool

not : Bool -> Bool
not true = false
not false = true

!_ : Bool -> Bool
! true = false
! false = true

if_then_else : {A : Set} -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y

data Nat : Set where
     zero : Nat
     suc : Nat -> Nat

add : Nat -> Nat -> Nat
add zero y = y
add (suc y) y' = suc (add y y')

_+_  : Nat -> Nat -> Nat
zero +  y = y
(suc y) + y' = suc (y + y')

low = suc zero

high = low + (low + low)




