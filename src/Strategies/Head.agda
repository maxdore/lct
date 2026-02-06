{-# OPTIONS --guardedness #-}

module Strategies.Head where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing ; is-just)
open import Data.List as List using (List ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl ; cong ; cong₂)
open import Data.Bool
open import Data.Product

open import Base
open import Relations.LambdaBeta
open import Strategies.Base
-- open import Strategies.Leftmost

head : Strategy
head = {!!}


-- head→left : ∀{n} → (s : Λ n) → T (is-just (head s)) → T (is-just (leftmost s))
-- head→left = {!!}



Solvable : ∀{n} → (s : Λ n) → Set
Solvable {n} s = Σ (List (Λ n)) λ ts → β⊢ (List.foldl _∙_ s ts) ＝ (ƛ (ν zero))


hnf→Solvable :  ∀{n} → (s : Λ n) → Finite (reduction head s) → Solvable s
hnf→Solvable = {!!}
