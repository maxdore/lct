module Types.ChurchTypes where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Vec as Vec using (Vec ; [] ; _∷_) renaming (lookup to _!_)
open import Data.Product

open import Base
open import Types.Base

open import Data.Bool



_Typeq_ : Typ → Typ → Bool
A Typeq B = {!!}


abs0 : (Typ → ℕ) → Typ → Typ → ℕ
abs0 V A B with A Typeq B
... | false = V B
... | true = suc (V A)



data Λ_of_ : (Typ → ℕ) → Typ → Set where
  ν : ∀{A} {V : Typ → ℕ} → Fin (V A) → Λ V of A
  _∙_ : ∀{A B} {V : Typ → ℕ}
    → (s : Λ V of A ⇒ B)
    → (t : Λ V of A)
    → Λ V of B
  ƛ : ∀{A B} {V : Typ → ℕ}
    → (s : Λ abs0 V A of B)
    → Λ V of A ⇒ B

infixl 0 Λ_of_

Church→Curry : ∀{V A} → Λ V of A → Σ[ Γ ∈ Ctxt {!!} ] Σ[ s ∈ Λ {!!} ] (Γ ⊢ s ∶ A)
Church→Curry = {!!}


Curry→Church : ∀{n A} → (Γ : Ctxt n) → (s : Λ n) → (Γ ⊢ s ∶ A) → Λ {!!} of A
Curry→Church = {!!}

