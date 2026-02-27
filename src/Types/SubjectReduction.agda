module Types.SubjectReduction where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Vec as Vec using (Vec ; [] ; _∷_) renaming (lookup to _!_)

open import Base
open import Relations.BetaRed
open import Types.Base


SubjectReduction : ∀{n Γ A} → (s t : Λ n) {u : Λ (suc n)} {v : Λ n}
  → Γ ⊢ (ƛ u) ∙ v ∶ A
  → Γ ⊢ u [ v / zero ] ∶ A
SubjectReduction = {!!}
