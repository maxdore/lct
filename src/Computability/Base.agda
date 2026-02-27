module Computability.Base where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl ; cong ; cong₂)
open import Relation.Unary
open import Relation.Nullary

open import Base
open import Relations.LambdaBeta
open import Examples

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


SndRecThm : (f : Λ 0) → Σ[ u ∈ Λ 0 ] (β⊢ f ∙ ⌜⌜ u ⌝⌝ ＝ u)
SndRecThm = {!!}


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

