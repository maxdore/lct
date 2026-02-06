module Relations.Base where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Product

open import Base


Rel : Set → Set₁
Rel A = A → A → Set

data ReflTrans {A : Set} (R : Rel A) : Rel A where
  inj : ∀{s t} → R s t → ReflTrans R s t
  refl : ∀{s} → ReflTrans R s s
  trans : ∀{s t u} → ReflTrans R s t → ReflTrans R t u → ReflTrans R s u

data ReflTransSym {A : Set} (R : Rel A) : Rel A where
  inj : ∀{s t} → R s t → ReflTransSym R s t
  refl : ∀{s} → ReflTransSym R s s
  sym : ∀{s t} → ReflTransSym R s t → ReflTransSym R t s
  trans : ∀{s t u} → ReflTransSym R s t → ReflTransSym R t u → ReflTransSym R s u


Diamond : ∀{A} → Rel A → Set
Diamond {A} _R_ = (s t₁ t₂ : A)
  → s R t₁
  → s R t₂
  → Σ[ u ∈ A ] (t₁ R u) × (t₂ R u)

ChurchRosser : ∀{A} → Rel A → Set
ChurchRosser R = Diamond (ReflTrans R)

RelΛ = {n : ℕ} → Rel (Λ n)


data Compat (R : RelΛ) : RelΛ where
  inj : ∀{n}{s t : Λ n}
    → R s t
    → Compat R s t
  left : ∀{n}{s t u : Λ n}
    → Compat R s t
    → Compat R (s ∙ u) (t ∙ u)
  right : ∀{n}{s t u : Λ n}
    → Compat R s t
    → Compat R (u ∙ s) (u ∙ t)
  abs : ∀{n}{s t : Λ (suc n)}
    → Compat R {suc n} s t
    → Compat R (ƛ s) (ƛ t)


