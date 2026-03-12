module Weaken where

open import Data.Empty
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Fin.Properties as FinP using (toℕ<n ; toℕ-fromℕ ; <-irrefl ; suc-injective ; 0≢1+n)
open import Data.Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)


open import Base
open import Relations.LambdaBeta

-- A module to take terms of Λ n to type Λ (n + 1)
-- and show that substitution back for variable n does nothing

weaken : ∀ {n} → Λ n → Λ (suc n)
weaken (ν x) = ν (Fin.inject₁ x)
weaken (f ∙ f₁) = (weaken f) ∙ (weaken f₁)
weaken (ƛ f) = ƛ (weaken f)

liftEqiv : ∀{n}{s t : Λ n} → s ≡ t → (β⊢ s ＝ t)
liftEqiv {s = s} h = Eq.subst (β⊢ s ＝_) h refl

inject₁Fromℕ : ∀{y : ℕ} → (x : Fin y) → (Fin.inject₁ x) Fin.< (Fin.fromℕ y)
inject₁Fromℕ {y} x = Eq.subst (λ k → Fin.toℕ (Fin.inject₁ x) Nat.< k) (Eq.sym (toℕ-fromℕ y )) (FinP.inject₁ℕ< x) 

justNotNothing : ∀ {ℓ}{A : Set ℓ}{a : A} → (just a ≡ nothing) → ⊥
justNotNothing ()

substVarNothing : ∀{n} → {a b : Fin (suc n)} → (substVar a b ≡ nothing) → (a ≡ b)
substVarNothing {a = zero} {b = zero} h = refl
substVarNothing {suc n} {zero} {suc j} h = ⊥-elim (justNotNothing h)
substVarNothing {suc n} {suc i} {zero} h = ⊥-elim (justNotNothing h)
substVarNothing {suc n} {suc i} {suc j} h with substVar i j in eq
... | nothing = Eq.cong suc (substVarNothing eq)

substVarDestruct : ∀{n} → (x y : Fin (suc n)) → (z : Fin n) → (substVar (suc x) (suc y) ≡ just (suc z)) → (substVar x y ≡ just z)
substVarDestruct x y z h with substVar x y in eq
... | just z0 = Eq.cong just (suc-injective (just-injective h))

substVarJustZero : ∀{n} → (x y : Fin (suc (suc n))) → (substVar (suc x) (suc y) ≡ just zero) → ⊥
substVarJustZero x y h with substVar x y in eq
... | just z = 0≢1+n (just-injective (Eq.trans (Eq.sym h) refl))

substVarJust : ∀{n} → (x z : Fin (suc n)) → (substVar (Fin.inject₁ x) (suc (Fin.fromℕ n)) ≡ just z) → (x ≡ z)
substVarJust zero z h = just-injective h
substVarJust {suc n'} (suc x') zero h = ⊥-elim (substVarJustZero (Fin.inject₁ x') (Fin.fromℕ (suc n')) h)
substVarJust {suc n'} (suc x') (suc z') h = Eq.cong suc (substVarJust x' z' (substVarDestruct (Fin.inject₁ x') (Fin.fromℕ (suc n')) z' h))

weakenSub : ∀{n}{s s' : Λ n} → β⊢ ((weaken s) [ s' / Fin.fromℕ n ]) ＝ s
weakenSub {suc n'} {ν x} {s'} with substVar (Fin.inject₁ x) (Fin.fromℕ (suc n')) in eq
... | nothing = ⊥-elim (<-irrefl (substVarNothing eq) (inject₁Fromℕ x)) 
... | just z = Eq.subst (λ k → β⊢ ν z ＝ ν k) (Eq.sym (substVarJust x z eq)) refl
weakenSub {s = f ∙ f₁} = app weakenSub weakenSub
weakenSub {s = ƛ s₁} = abs weakenSub
