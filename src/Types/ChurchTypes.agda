module Types.ChurchTypes where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Vec as Vec using (Vec ; [] ; _∷_) renaming (lookup to _!_)
open import Data.Product

open import Base
open import Types.Base

data Λ_of_ : (n : ℕ) → Typ → Set where
  ν :  ∀{n} → Fin n → {A : Typ} → Λ n of A
  _∙_ : ∀{n A B}
    → (s : Λ n of A ⇒ B)
    → (t : Λ n of A)
    → Λ n of B
  ƛ : ∀{n} {A B}
    → (s : Λ (suc n) of B)
    → Λ n of A ⇒ B

infixl 0 Λ_of_



Church→Curry : ∀{n A} → Λ n of A → Σ[ Γ ∈ Ctxt n ] Σ[ s ∈ Λ n ] (Γ ⊢ s ∶ A)
Church→Curry = {!!}


Curry→Church : ∀{n A} → (Γ : Ctxt n) → (s : Λ n) → (Γ ⊢ s ∶ A) → Λ n of A
Curry→Church = {!!}

