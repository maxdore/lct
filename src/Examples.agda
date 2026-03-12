{-# OPTIONS --allow-unsolved-metas #-}
module Examples where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Bool
open import Data.Empty
open import Data.Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Fin.Properties as FinP using (suc-injective)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl ; cong ; cong₂)

open import Base
open import Relations.LambdaBeta
open import Weaken

tK fK : Λ 0
tK = ƛ (ƛ (ν (suc zero)))
fK = ƛ (ƛ (ν zero))

x̸≡m : ∀{m} → (x : Fin m) → (Fin.inject₁ x ≡ Fin.fromℕ m) → ⊥
x̸≡m x h = FinP.fromℕ≢inject₁ (Eq.sym h)

substVarDestruct' : ∀{m} → (x z : Fin (suc m)) → (substVar (Fin.inject₁ (suc x)) (Fin.fromℕ (suc (suc m))) ≡ just (suc z)) → (substVar (Fin.inject₁ x) (Fin.fromℕ (suc m)) ≡ just z)
substVarDestruct' {m} x z h with substVar (Fin.inject₁ x) (Fin.fromℕ (suc m)) in eq
... | just z' = Eq.cong just (suc-injective (just-injective h))

substVarJust' : ∀{m} → (x z : Fin m) → (substVar (Fin.inject₁ x) (Fin.fromℕ m) ≡ just z) → (x ≡ z)
substVarJust' zero z h = just-injective h
substVarJust' {suc (suc m')} (suc x) zero h = ⊥-elim (substVarJustZero (Fin.inject₁ x) (Fin.fromℕ (suc m')) h)
substVarJust' {suc (suc m')} (suc x) (suc z) h = Eq.cong suc (substVarJust' x z (substVarDestruct' x z h))

injectSub : ∀{m} → (b : Λ m) → (x : Fin m) → (ν (Fin.inject₁ x) [ b / (Fin.fromℕ m) ] ≡ (ν x))
injectSub {m} b x with substVar (Fin.inject₁ x) (Fin.fromℕ m) in eq
... | just z = Eq.cong ν (Eq.sym (substVarJust' x z eq))
... | nothing = ⊥-elim (x̸≡m x (substVarNothing eq))

lessxm : ∀{m} → (x : Fin m) → (less x (Fin.fromℕ m) ≡ false) → ⊥
lessxm {suc m} zero ()
lessxm {suc m} (suc x) h = lessxm x h

tKappLemma : ∀{m} → (a b : Λ m) → (β⊢ lift a (Fin.fromℕ m) [ b / (Fin.fromℕ m) ] ＝ a)
tKappLemma {m} (ν x) b with less x (Fin.fromℕ m) in hless
... | true = liftEqiv (injectSub b x)
... | false = ⊥-elim (lessxm x hless)
tKappLemma (a ∙ a₁) b = app (tKappLemma a b) (tKappLemma a₁ b)
tKappLemma (ƛ a) b = abs (tKappLemma a (lift b zero))

tKapp : ∀{a b : Λ 0} → (β⊢ tK ∙ a ∙ b ＝ a)
tKapp {a} {b} = trans (app β refl) (trans (app (abs refl) refl) (trans β (tKappLemma a b)))

fKapp : ∀{a b : Λ 0} → (β⊢ fK ∙ a ∙ b ＝ b)
fKapp {a} {b} = trans (app (trans β (abs refl)) refl) β


expSubst = s [ t / suc zero ] where
  s : Λ 3
  s = ν zero ∙ ν (suc zero) ∙ ν (suc (suc zero)) ∙ (ƛ (ν zero ∙ ν (suc (suc zero))))
  t : Λ 2
  t = ƛ (ν (suc zero) ∙ ν zero)

