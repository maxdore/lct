module Relations.BetaRedImpl where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Product

open import Base
open import Relations.Base
open import Relations.LambdaBeta
open import Relations.BetaRed


-- Lemma that shows =β treats application as expected 
lem1 : ∀{n} (s s' t t' : Λ n) → (s ＝β s') → (t ＝β t') → ((s ∙ t) ＝β (s' ∙ t'))
lem1 s s' t t' (inj x₁) (inj x₂) = trans (inj (left x₁)) (inj (right x₂))
lem1 s s' t t (inj x) refl = inj (left x)
lem1 s s' t t' (inj x₁) (sym x₂) = trans (sym (lem1 s s t' t refl x₂)) (inj (left x₁))
lem1 s s' t t' x₁ (trans {t} {u} {t'} x₂ x₃) = trans (lem1 s s' t u x₁ x₂) (lem1 s' s' u t' refl x₃)
lem1 s s t t' refl (inj x) = inj (right x)
lem1 s s t t refl refl = refl
lem1 s s t t' refl (sym x) = sym (lem1 s s t' t refl x)
lem1 s s' t t' (sym x₁) (inj x₂) = (trans (sym (lem1 s' s t t x₁ refl)) (inj (right x₂)))
lem1 s s' t t (sym x) refl = sym (lem1 s' s t t x refl)
lem1 s s' t t' (sym x₁) (sym x₂) = sym (lem1 s' s t' t x₁ x₂)
lem1 s s' t t' (trans {s} {u} {s'} x₁ x₂) (inj x₃) = trans (trans (lem1 s u t t x₁ refl) (inj (right x₃))) (lem1 u s' t' t' x₂ refl)
lem1 s s' t t (trans {s} {u} {s'} x₁ x₂) refl = trans (lem1 s u t t x₁ refl) (lem1 u s' t t x₂ refl)
lem1 s s' t t' (trans {s} {u} {s'} x₁ x₂) (sym x₃) = trans (trans (lem1 s u t t x₁ refl) (sym (lem1 u u t' t refl x₃))) (lem1 u s' t' t' x₂ refl)

-- Lemma that shows =β treats abstraction as expected
lem2 : ∀{n} (s t : Λ (suc n)) → (s ＝β t) → ((ƛ s) ＝β (ƛ t))
lem2 s t (inj x) = inj (abs x)
lem2 s s refl = refl
lem2 s t (sym x) = sym (lem2 t s x)
lem2 s t (trans {s} {u} {t} x₁ x₂) = trans (lem2 s u x₁) (lem2 u t x₂)


β⊢＝→＝β : ∀{n} (s t : Λ n) → β⊢ s ＝ t → s ＝β t
β⊢＝→＝β s s refl = ReflTransSym.refl
β⊢＝→＝β s t (sym x) = ReflTransSym.sym (β⊢＝→＝β t s x)
β⊢＝→＝β s t (trans {s} {u} {t} x₁ x₂) = ReflTransSym.trans (β⊢＝→＝β s u x₁) (β⊢＝→＝β u t x₂)
β⊢＝→＝β (s ∙ t) (s' ∙ t') (app {s} {s'} {t} {t'} x₁ x₂) = lem1 s s' t t' (β⊢＝→＝β s s' x₁) (β⊢＝→＝β t t' x₂)
β⊢＝→＝β (ƛ s) (ƛ t) (abs x) = lem2 s t (β⊢＝→＝β s t x)
β⊢＝→＝β ((ƛ s) ∙ t) .(s [ t / zero ]) β = inj (inj β)


-- Lemma that shows s ⇨β t (1 step beta reduction) implies β⊢ s ＝ t
lem3 : ∀{n} (s t : Λ n) → (Compat βᴿ s t) → (β⊢ s ＝ t)
lem3 ((ƛ s) ∙ t)  .(s [ t / zero ]) (inj β) = β
lem3 (s ∙ u) (t ∙ u) (left x) = app (lem3 s t x) refl
lem3 (u ∙ s) (u ∙ t) (right x) = app refl (lem3 s t x)
lem3 (ƛ s) (ƛ t) (abs x) = abs (lem3 s t x)


＝β→β⊢＝ : ∀{n} (s t : Λ n) → s ＝β t → β⊢ s ＝ t
＝β→β⊢＝ s t (inj x) = lem3 s t x
＝β→β⊢＝ s s refl = refl
＝β→β⊢＝ s t (sym x) = sym (＝β→β⊢＝ t s x)
＝β→β⊢＝ s t (trans {s} {u} {t} x₁ x₂) = trans (＝β→β⊢＝ s u x₁) (＝β→β⊢＝ u t x₂)