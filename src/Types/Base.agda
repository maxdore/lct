module Types.Base where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Vec as Vec using (Vec ; [] ; _∷_) renaming (lookup to _!_)


open import Base

-- Unicode: \nu and \Rightarrow
data Typ : Set where
  ν : ℕ → Typ
  _⇒_ : Typ → Typ → Typ


Ctxt : ℕ → Set
Ctxt n = Vec Typ n

data _⊢_∶_ : ∀{n} → Ctxt n → Λ n → Typ → Set where
  var : ∀{n}{Γ : Ctxt n} {x : Fin n}
    → Γ ⊢ ν x ∶ (Γ ! x)
  app : ∀{n}{Γ : Ctxt n} {A B} {s t}
    → Γ ⊢ s ∶ A ⇒ B
    → Γ ⊢ t ∶ A
    → Γ ⊢ s ∙ t ∶ B
  lam : ∀{n}{Γ : Ctxt n} {A B} {s : Λ (suc n)}
    → A ∷ Γ ⊢ s ∶ B
    → Γ ⊢ ƛ s ∶ A ⇒ B

infixl 0 _⊢_∶_


