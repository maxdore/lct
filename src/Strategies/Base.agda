{-# OPTIONS --guardedness #-}

module Strategies.Base where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing ; is-just)
open import Data.List as List using (List ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl ; cong ; cong₂)
open import Data.Bool
open import Data.Product

open import Base


Strategy : Set
Strategy = {n : ℕ} → Λ n → Maybe (Λ n)


record Colist (A : Set) : Set where
  coinductive
  field
    uncons : Maybe (A × Colist A)
open Colist


reduction : Strategy → {n : ℕ} → (s : Λ n) → Colist (Λ n)
reduction red {n} s .uncons with red s
... | nothing = nothing
... | just s' = just (s' , reduction red s')



data Finite {A : Set} : Colist A → Set where
  fin-nil  : ∀ {xs}
    → uncons xs ≡ nothing
    → Finite xs

  fin-cons : ∀ {xs a xs'}
    → uncons xs ≡ just (a , xs')
    → Finite xs'
    → Finite xs




