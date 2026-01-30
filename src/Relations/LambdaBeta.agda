module Relations.LambdaBeta where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)

open import Base

data β⊢_＝_  {n : ℕ} : Rel (Λ n) where
  refl : ∀{s} → β⊢ s ＝ s
  sym : ∀{s t} → β⊢ s ＝ t → β⊢ t ＝ s
  trans : ∀{s t u}
    → β⊢ s ＝ t → β⊢ t ＝ u → β⊢ s ＝ u
  app : ∀{s s' t t'}
    → β⊢ s ＝ s' → β⊢ t ＝ t'
    → β⊢ (s ∙ t) ＝ (s' ∙ t')
  abs : ∀{s t}
    → β⊢ s ＝ t
    → β⊢ ƛ s ＝ ƛ t
  β : ∀{s : Λ (suc n)} {t : Λ n}
    → β⊢ ((ƛ s) ∙ t) ＝ (s [ t / zero ])
