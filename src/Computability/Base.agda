module Computability.Base where

open import Data.Nat as Nat using (ℕ ; zero ; suc; z<s; s<s)
open import Data.Nat.Properties as ℕₚ using (<-irrefl)
open import Data.Fin.Properties as FinP using (<-irrefl; toℕ-fromℕ; toℕ-cancel-<)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Empty
open import Data.Maybe.Properties as MaybeP using (just-injective)
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl ; cong ; cong₂; subst)
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

weakenFin : ∀ {n} → Fin n → Fin (suc n)
weakenFin zero = zero
weakenFin (suc i) = suc (weakenFin i)

weaken : ∀ {n} → Λ n → Λ (suc n)
weaken (ν x) = ν (weakenFin x)
weaken (f ∙ f₁) = (weaken f) ∙ (weaken f₁)
weaken (ƛ f) = ƛ (weaken f)

t : (f : Λ 0) → Λ 0
t f = ƛ ((weaken f) ∙ ((weaken appK) ∙ ν zero ∙ ((weaken gnumK) ∙ ν zero)))

u : (f : Λ 0) → Λ 0
u f = t f ∙ ⌜⌜ t f ⌝⌝

liftEqiv : ∀{n}{s t : Λ n} → s ≡ t → (β⊢ s ＝ t)
liftEqiv {s = s} {t = t} h = Eq.subst (β⊢ s ＝_) h refl

FinZeroEmpty : ∀ {ℓ} {A : Set ℓ} → (x : Fin 0) → A
FinZeroEmpty ()

toℕ<Fin : ∀{y : ℕ} → (x : Fin y) → (Fin.toℕ x) Nat.< (y)
toℕ<Fin {y = zero} ()
toℕ<Fin {suc y'} zero = Nat.z<s
toℕ<Fin {suc y'} (suc n) = Nat.s<s (toℕ<Fin n)

toℕ<Fin' : ∀{y : ℕ} → (x : Fin y) → (Fin.toℕ x) Nat.< (Fin.toℕ (Fin.fromℕ y))
toℕ<Fin' {y = y} x = Eq.subst (λ k → (Fin.toℕ x) Nat.< k) (Eq.sym (toℕ-fromℕ y)) (toℕ<Fin x) 

toℕWeaken : ∀{y : ℕ} → (x : Fin y) → Fin.toℕ x ≡ Fin.toℕ (weakenFin x)
toℕWeaken {y = zero} ()
toℕWeaken {suc y'} zero = refl
toℕWeaken {suc y'} (suc n) = Eq.subst (λ k → Fin.toℕ (suc n) ≡ k) refl (Eq.cong suc (toℕWeaken n)) 

weakenFinFromℕ : ∀{y : ℕ} → (x : Fin y) → (weakenFin x) Fin.< (Fin.fromℕ y)
weakenFinFromℕ {y = y} x = Eq.subst (λ k → k Nat.< Fin.toℕ (Fin.fromℕ y))  (toℕWeaken x) (toℕ<Fin' x)

impossible' : ∀ {ℓ}{A : Set ℓ}{y : ℕ} → (x : Fin y) → ((weakenFin x) ≡ Fin.fromℕ y) → A
impossible' x p = ⊥-elim (FinP.<-irrefl p (weakenFinFromℕ x))

justNotNothing : ∀ {ℓ}{A : Set ℓ}{a : A} → (just a ≡ nothing) → ⊥
justNotNothing ()

substVarNothing : ∀{n} → (a b : Fin (suc n)) → (substVar a b ≡ nothing) → (a ≡ b)
substVarNothing zero zero h = refl
substVarNothing {suc n} zero (suc j) h = ⊥-elim (justNotNothing h)
substVarNothing {suc n} (suc i) zero h = ⊥-elim (justNotNothing h)
substVarNothing {suc n} (suc i) (suc j) h with substVar i j in eq
... | nothing = Eq.cong suc (substVarNothing i j eq)
... | just k = ⊥-elim (justNotNothing h)

impossibleJust : ∀{n} → (z : Fin (suc n)) → (Maybe.map suc nothing ≡ just z) → ⊥
impossibleJust z ()

substVarDestruct : ∀{n} → (x y : Fin (suc n)) → (z : Fin n) → (substVar (suc x) (suc y) ≡ just (suc z)) → (substVar x y ≡ just z)
substVarDestruct x y z h with substVar x y in eq
... | nothing = ⊥-elim (impossibleJust (suc z) h)
... | just z0 = Eq.cong just (FinP.suc-injective (just-injective h))

substVarJustZero : ∀{n} → (x y : Fin (suc (suc n))) → (substVar (suc x) (suc y) ≡ just zero) → ⊥
substVarJustZero x y h with substVar x y in eq
... | nothing = impossibleJust (zero) h
... | just z = FinP.0≢1+n (just-injective (Eq.trans (Eq.sym h) refl))

substVarJust : ∀{n} → (x z : Fin (suc n)) → (substVar (weakenFin x) (suc (Fin.fromℕ n)) ≡ just z) → (x ≡ z)
substVarJust zero z h = just-injective h
substVarJust {zero} (suc x') z h = FinZeroEmpty x'
substVarJust {suc n'} (suc x') zero h = ⊥-elim (substVarJustZero (weakenFin x') (Fin.fromℕ (suc n')) h)
substVarJust {suc n'} (suc x') (suc z') h = Eq.cong suc (substVarJust x' z' (substVarDestruct (weakenFin x') (Fin.fromℕ (suc n')) z' h))

weakenSub0 : ∀{n}{s s' : Λ n} → β⊢ ((weaken s) [ s' / Fin.fromℕ n ]) ＝ s
weakenSub0 {n = 0} {s = ν x} = FinZeroEmpty x
weakenSub0 {n = suc n'} {s = ν x} {s' = s'} with substVar (weakenFin x) (Fin.fromℕ (suc n')) in eq
... | nothing = impossible' x (substVarNothing (weakenFin x) (Fin.fromℕ (suc n')) eq)
... | just z = Eq.subst (λ k → β⊢ ν z ＝ ν k) (Eq.sym (substVarJust x z eq)) refl
weakenSub0 {s = f ∙ f₁} = app weakenSub0 weakenSub0
weakenSub0 {s = ƛ s₁} = abs weakenSub0

theExpand : (f : Λ 0) → (β⊢ ((((weaken f) ∙ ((weaken appK) ∙ ν zero ∙ ((weaken gnumK) ∙ ν zero)))) [ ⌜⌜ t f ⌝⌝ / zero ]) ＝ (f ∙ (appK ∙ ⌜⌜ t f ⌝⌝  ∙ (gnumK ∙ ⌜⌜ t f ⌝⌝ ))))
theExpand f = trans (liftEqiv Eq.refl) (app weakenSub0 (app (app weakenSub0 refl) (app weakenSub0 refl)))

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

