module Combinatory.WeakRedThms where

open import Agda.Builtin.Nat using (_<_ ; _==_)
open import Data.Nat as Nat hiding (_<_) -- using (ℕ ; zero ; suc ; _⊔′_ ; _+_)
open import Data.Nat.Properties
open import Data.Fin as Fin using (Fin ; zero ; suc ; toℕ ; fromℕ)
open import Data.Product
open import Data.Bool as Bool using (true ; false ; _∨_ ; T ; not)
-- open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; cong ; cong₂)
open import Relation.Nullary using (¬_)


open import Base
open import Relations.Base
open import Relations.BetaRed
open import Relations.LambdaBeta
open import Combinatory.Base

-- pf that CL⊢＝ <=> =w follows pattern from https://github.com/maxdore/lct/pull/2

＝wDoesApp : (A A' B B' : CL) → (A ＝w A') → (B ＝w B') → ((A ∙ B) ＝w (A' ∙ B'))
＝wDoesApp A A' B B' (inj x) (inj x₁) = trans (inj (left x)) (inj (right x₁))
＝wDoesApp A A' B B' (inj x) refl = inj (left x)
＝wDoesApp A A' B B' (inj x) (sym pf) = trans (sym (＝wDoesApp A A B' B refl pf)) (inj (left x))
＝wDoesApp A A' B B' refl (inj x) = inj (right x)
＝wDoesApp A A' B B' refl refl = refl
＝wDoesApp A A  B B' refl (sym pf) = sym (＝wDoesApp A A B' B refl pf)
＝wDoesApp A A' B B' (sym pf) (inj x) = trans (inj (right x)) (sym (＝wDoesApp A' A B' B' pf refl))
＝wDoesApp A A' B B  (sym pf) refl = sym (＝wDoesApp A' A B B pf refl)
＝wDoesApp A A' B B' (sym pf) (sym pf₁) = sym (＝wDoesApp A' A B' B pf pf₁)
-- idea: (A ∙ B) ＝w (C ∙ B) ＝w (C ∙ B') ＝w (A' ∙ B')
＝wDoesApp A A' B B' (trans {A} {C} {A'} pf₁ pf₂) (inj x) = trans (trans (＝wDoesApp A C B B pf₁ refl) (inj (right x))) (＝wDoesApp C A' B' B' pf₂ refl)
＝wDoesApp A A' B B  (trans {A} {C} {A'} pf₁ pf₂) refl = trans (＝wDoesApp A C B B pf₁ refl) (＝wDoesApp C A' B B pf₂ refl)
-- idea: (A ∙ B) ＝w (C ∙ B) ＝w (C ∙ B') ＝w (A' ∙ B')
＝wDoesApp A A' B B' (trans {A} {C} {A'} pf₁ pf₂) (sym pf) = trans (trans (＝wDoesApp A C B B pf₁ refl) (sym (＝wDoesApp C C B' B refl pf))) (＝wDoesApp C A' B' B' pf₂ refl)

＝wDoesApp A A' B B' pf (trans {B} {C} {B'} pf₁ pf₂) = trans (＝wDoesApp A A' B C pf pf₁) (＝wDoesApp A' A' C B' refl pf₂)

CL⊢＝→＝w : (A B : CL) → CL⊢ A ＝ B → A ＝w B
CL⊢＝→＝w A B refl = refl
CL⊢＝→＝w A B (sym pf) = sym (CL⊢＝→＝w B A pf)
CL⊢＝→＝w A B (trans {A} {C} {B} pf pf₁) = trans (CL⊢＝→＝w A C pf) (CL⊢＝→＝w C B pf₁)
CL⊢＝→＝w A B (app {A₁} {A₂} {B₁} {B₂} pf pf₁) = ＝wDoesApp A₁ A₂ B₁ B₂ (CL⊢＝→＝w A₁ A₂ pf) (CL⊢＝→＝w B₁ B₂ pf₁)
CL⊢＝→＝w A B Krule = inj (inj wK)
CL⊢＝→＝w A B Srule = inj (inj wS)

⇨w→CL⊢＝ : (A B : CL) → CompatCL wᴿ A B → CL⊢ A ＝ B
⇨w→CL⊢＝ A B (inj wK) = Krule
⇨w→CL⊢＝ A B (inj wS) = Srule
⇨w→CL⊢＝ (A ∙ C) (B ∙ C) (left pf) = app (⇨w→CL⊢＝ A B pf) refl
⇨w→CL⊢＝ (C ∙ A) (C ∙ B) (right pf) = app refl (⇨w→CL⊢＝ A B pf)

＝w→CL⊢＝ : (A B : CL) → A ＝w B → CL⊢ A ＝ B
＝w→CL⊢＝ A B (inj x) = ⇨w→CL⊢＝ A B x
＝w→CL⊢＝ A B refl = refl
＝w→CL⊢＝ A B (sym pf) = sym (＝w→CL⊢＝ B A pf)
＝w→CL⊢＝ A B (trans {A} {C} {B} pf pf₁) = trans (＝w→CL⊢＝ A C pf) (＝w→CL⊢＝ C B pf₁)




⇨wCR : ChurchRosser (CompatCL wᴿ)
⇨wCR s t₁ t₂ sWt₁ sWt₂ = {!   !} , ({!   !} , {!   !})




-- ⇨w→ƛ↠βƛ : (A B : CL) → A ⇨w B → ＜ A ＞ƛ ↠β ＜ B ＞ƛ
-- ⇨w→ƛ↠βƛ = {!   !}

-- =w→ƛ=βƛ : (A B : CL) → A ＝w B → ＜ A ＞ƛ ＝β ＜ B ＞ƛ
-- =w→ƛ=βƛ = {!   !}
