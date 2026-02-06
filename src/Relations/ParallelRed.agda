module Relations.ParallelRed where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)

open import Base
open import Relations.Base


data _||_ : RelΛ where
  refl : ∀{n}{s : Λ n} → s || s
  app : ∀{n}{s s' t t' : Λ n}
    → s || s'
    → t || t'
    → (s ∙ t) || (s' ∙ t')
  abs : ∀ {n} {s s' : Λ (suc n)}
    → s || s'
    → ƛ s || ƛ s'
  ||β : ∀{n}{s s' : Λ (suc n)} {t t' : Λ n}
    → s || s'
    → t || t'
    → ((ƛ s) ∙ t) || (s' [ t' / zero ])


||Diamond : ∀{n} → Diamond (_||_ {n = n})
||Diamond = {!!}
