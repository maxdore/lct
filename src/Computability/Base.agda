module Computability.Base where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl ; cong ; cong₂)
open import Relation.Unary
open import Relation.Nullary

open import Base
open import Relations.LambdaBeta
open import Examples
open import Weaken

-- unicode cul and cur
⌜_⌝ : ℕ → Λ 0
⌜ n ⌝ = ƛ (ƛ (apps n)) where
  apps : ℕ → Λ 2
  apps zero = ν zero
  apps (suc n) = ν (suc zero) ∙ apps n

-- unicode sharp
postulate
  ♯ : ∀{n} → Λ n → ℕ

⌜⌜_⌝⌝ : ∀{n} → Λ n → Λ 0
⌜⌜ n ⌝⌝ = ⌜ ♯ n ⌝


is-var : ℕ → ℕ
is-var = λ x → {!!}

is-varK : Λ 0
is-varK = {!!}


postulate
  appK : Λ 0
  appKβ : ∀{n}{s t : Λ n} → appK ∙ ⌜⌜ s ⌝⌝ ∙ ⌜⌜ t ⌝⌝ ≡ ⌜⌜ s ∙ t ⌝⌝
  gnumK : Λ 0
  gnumKβ : ∀{n}{s : Λ n} → gnumK ∙ ⌜⌜ s ⌝⌝ ≡ ⌜⌜ ⌜⌜ s ⌝⌝ ⌝⌝

t : (f : Λ 0) → Λ 0
t f = ƛ ((weaken f) ∙ ((weaken appK) ∙ ν zero ∙ ((weaken gnumK) ∙ ν zero)))

u : (f : Λ 0) → Λ 0
u f = t f ∙ ⌜⌜ t f ⌝⌝

theExpand : (f : Λ 0) → (β⊢ ((((weaken f) ∙ ((weaken appK) ∙ ν zero ∙ ((weaken gnumK) ∙ ν zero)))) [ ⌜⌜ t f ⌝⌝ / zero ]) ＝ (f ∙ (appK ∙ ⌜⌜ t f ⌝⌝  ∙ (gnumK ∙ ⌜⌜ t f ⌝⌝ ))))
theExpand f = trans (liftEqiv Eq.refl) (app weakenSub (app (app weakenSub refl) (app weakenSub refl)))

SndRecThmHolds : (f : Λ 0) → (β⊢ (t f ∙ (⌜⌜ t f ⌝⌝)) ＝ (f ∙ ⌜⌜ t f ∙ (⌜⌜ t f ⌝⌝ ) ⌝⌝))
SndRecThmHolds f = trans β (trans (theExpand f) (trans (app refl (app (refl) (liftEqiv gnumKβ))) ((app refl (liftEqiv appKβ))))) 

SndRecThm : (f : Λ 0) → Σ[ u ∈ Λ 0 ] (β⊢ f ∙ ⌜⌜ u ⌝⌝ ＝ u)
SndRecThm f = u f , sym (SndRecThmHolds f)

Λprop : (A : Λ 0 → Set) → Set
Λprop A = (s t : Λ 0) → β⊢ s ＝ t → A s → A t

non-trivial : (A : Λ 0 → Set) → Set
non-trivial A = (s t : Λ 0) → A s × ¬ (A t)

ScottCurry : (A : Λ 0 → Set)
  → Λprop A
  → non-trivial A
  → (f : Λ 0)
  → (A? : (s : Λ 0) → Dec (A s))
  → ((s : Λ 0) → A s → β⊢ f ∙ ⌜⌜ s ⌝⌝ ＝ tK)
  → ((s : Λ 0) → ¬ (A s) → β⊢ f ∙ ⌜⌜ s ⌝⌝ ＝ fK)
  → ⊥
ScottCurry = {!!}

