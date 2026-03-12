module Computability.Base where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Empty
open import Data.Product using (Σ ; Σ-syntax ; _,_ ; proj₁ ; proj₂ ; _×_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl ; cong ; cong₂)
open import Relation.Unary
open import Relation.Nullary
open import Data.Bool using (true ; false)

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
non-trivial A = (Σ[ s ∈ Λ 0 ] (Σ[ t ∈ Λ 0 ] (A s × ¬ (A t))))

ΛpropFalse : {A : Λ 0 → Set}{s t : Λ 0} → Λprop A → β⊢ s ＝ t → ¬ (A s) → ¬ (A t)
ΛpropFalse {s = s}{t = t} hΛ heq h¬As hAt = h¬As (hΛ t s (sym heq) hAt)

casing : (A : Λ 0 → Set) → (s : Λ 0) → Dec (A s) → (A s → ⊥) → ((A s →  ⊥) → ⊥) → ⊥
casing A s A? onYes onNo with A?
... | yes a = onYes a
... | no ¬a = onNo ¬a

g : (f a b : Λ 0) → Λ 0
g f a b = ƛ (((weaken f ∙ ν zero) ∙ weaken b) ∙ weaken a)

gApp : (f a b u : Λ 0) → (β⊢ ((g f a b) ∙ u) ＝ (f ∙ u ∙ b ∙ a))
gApp f a b u = trans β (app (app (app weakenSub refl) weakenSub) weakenSub)

Au : (A : Λ 0 → Set)
  → (a b u f : Λ 0)
  → ((s : Λ 0) → A s → β⊢ f ∙ ⌜⌜ s ⌝⌝ ＝ tK)
  → (β⊢ (g f a b) ∙ ⌜⌜ u ⌝⌝ ＝ u)
  → ¬ (A b)
  → Λprop A
  → A u → ⊥
Au A a b u f htK hgu h¬Ab hΛ hAu = ΛpropFalse hΛ (trans (trans (sym (tKapp)) (trans (sym (app (app (htK u hAu) refl) refl)) (sym (gApp f a b ⌜⌜ u ⌝⌝)))) hgu) h¬Ab hAu

¬Au : (A : Λ 0 → Set)
  → (a b u f : Λ 0)
  → ((s : Λ 0) → ¬ (A s) → β⊢ f ∙ ⌜⌜ s ⌝⌝ ＝ fK)
  → (β⊢ (g f a b) ∙ ⌜⌜ u ⌝⌝ ＝ u)
  → A a
  → Λprop A
  → ¬ (A u) → ⊥
¬Au A a b u f hfK hgu hAa hΛ h¬Au = h¬Au (hΛ a u (trans (trans (sym (fKapp)) (trans (app (app (sym (hfK u h¬Au)) refl) refl) (sym (gApp f a b ⌜⌜ u ⌝⌝)))) hgu) hAa)


ScottCurry : (A : Λ 0 → Set)
  → Λprop A
  → non-trivial A
  → (f : Λ 0)
  → (A? : (s : Λ 0) → Dec (A s))
  → ((s : Λ 0) → A s → β⊢ f ∙ ⌜⌜ s ⌝⌝ ＝ tK)
  → ((s : Λ 0) → ¬ (A s) → β⊢ f ∙ ⌜⌜ s ⌝⌝ ＝ fK)
  → ⊥
ScottCurry A hΛ (a , (b , (ha , hb) ) ) f A? htK hfK = casing A (proj₁ uhu) (A? (proj₁ uhu)) (Au A a b (proj₁ uhu) f htK (proj₂ uhu) hb hΛ) (¬Au A a b (proj₁ uhu) f hfK (proj₂ uhu) ha hΛ)
  where uhu : Σ[ u ∈ Λ 0 ] (β⊢ (g f a b) ∙ ⌜⌜ u ⌝⌝ ＝ u)
        uhu = SndRecThm (g f a b)

