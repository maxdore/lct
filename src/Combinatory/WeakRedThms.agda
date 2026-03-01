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




↠wDoesApp : (A A' B B' : CL) → (A ↠w A') → (B ↠w B') → ((A ∙ B) ↠w (A' ∙ B'))
↠wDoesApp A A' B B' (inj x) (inj x₁) = trans (inj (left x)) (inj (right x₁))
↠wDoesApp A A' B B' (inj x) refl = inj (left x)
↠wDoesApp A A' B B' refl (inj x) = inj (right x)
↠wDoesApp A A' B B' refl refl = refl
↠wDoesApp A A' B B' (trans {A} {C} {A'} pf₁ pf₂) (inj x) = trans (trans (↠wDoesApp A C B B pf₁ refl) (inj (right x))) (↠wDoesApp C A' B' B' pf₂ refl)
↠wDoesApp A A' B B  (trans {A} {C} {A'} pf₁ pf₂) refl = trans (↠wDoesApp A C B B pf₁ refl) (↠wDoesApp C A' B B pf₂ refl)

↠wDoesApp A A' B B' pf (trans {B} {C} {B'} pf₁ pf₂) = trans (↠wDoesApp A A' B C pf pf₁) (↠wDoesApp A' A' C B' refl pf₂)



data _||cl_ : Rel CL where
  refl : {A : CL} → A ||cl A
  app : {A A' B B' : CL}
    → A ||cl A'
    → B ||cl B'
    → (A ∙ B) ||cl (A' ∙ B')
  ||K : {A A' B : CL}
    → A ||cl A'
    → (K ∙ A ∙ B) ||cl A'
  ||S : {A A' B B' C C' : CL}
    → A ||cl A'
    → B ||cl B'
    → C ||cl C'
    → (S ∙ A ∙ B ∙ C) ||cl (A' ∙ C' ∙ (B' ∙ C'))

||clDiamond : Diamond (_||cl_)
||clDiamond A A B refl pf = B , (pf , refl)

||clDiamond (A ∙ B) (A₁ ∙ B₁) (A₂ ∙ B₂) (app A||A₁ B||B₁) (app A||A₂ B||B₂) with (||clDiamond A A₁ A₂ A||A₁ A||A₂ , ||clDiamond B B₁ B₂ B||B₁ B||B₂)
... | ((A₃ , (A₁||A₃ , A₂||A₃)) , (B₃ , (B₁||B₃ , B₂||B₃))) = (A₃ ∙ B₃) , ((app A₁||A₃ B₁||B₃) , (app A₂||A₃ B₂||B₃))
||clDiamond (K ∙ A ∙ B) (A₂ ∙ B') A' (app pf pf₁) (||K pf₂) = {!   !}
||clDiamond A B₁ B₂ (app pf pf₁) (||S pf₂ pf₃ pf₄) = {!   !}

||clDiamond (K ∙ A ∙ B) B₁ (A₁ ∙ B₂) (||K pf) (app pf₂ pf₃) = A , ({!   !} , {!   !})
||clDiamond (K ∙ A ∙ _) A₁ A₂ (||K A||A₁) (||K A||A₂) with ||clDiamond A A₁ A₂ A||A₁ A||A₂
... | (A₃ , (A₁||A₃ , A₂||A₃)) = A₃ , (A₁||A₃ , A₂||A₃)

||clDiamond A B₁ B₂ (||S pf pf₁ pf₂) (app pf₃ pf₄) = {!   !}
||clDiamond (S ∙ A ∙ B ∙ C) (A₁ ∙ C₁ ∙ (B₁ ∙ C₁)) (A₂ ∙ C₂ ∙ (B₂ ∙ C₂)) (||S A||A₁ B||B₁ C||C₁) (||S A||A₂ B||B₂ C||C₂) 
    with (||clDiamond A A₁ A₂ A||A₁ A||A₂ , ||clDiamond B B₁ B₂ B||B₁ B||B₂)
... | ((A₃ , (A₁||A₃ , A₂||A₃)) , (B₃ , (B₁||B₃ , B₂||B₃))) 
        with ||clDiamond C C₁ C₂ C||C₁ C||C₂ 
...     | (C₃ , (C₁||C₃ , C₂||C₃)) = (A₃ ∙ C₃ ∙ (B₃ ∙ C₃)) , ((app (app A₁||A₃ C₁||C₃) (app B₁||B₃ C₁||C₃)) , app (app A₂||A₃ C₂||C₃) (app B₂||B₃ C₂||C₃))

||clDiamond A B A pf refl = B , (refl , pf)


||cl→||cl* : (A B : CL) → A ||cl B → ReflTrans _||cl_ A B
||cl→||cl* A B refl = refl
||cl→||cl* (A ∙ B) (A' ∙ B') (app pf pf₁) = trans (inj (app pf pf₁)) refl
||cl→||cl* A B (||K pf) = inj (||K pf)
||cl→||cl* A B (||S pf pf₁ pf₂) = inj (||S pf pf₁ pf₂)

⇨w→||cl : (A B : CL) → A ⇨w B → A ||cl B
⇨w→||cl A B (inj wK) = ||K refl
⇨w→||cl A B (inj wS) = ||S refl refl refl
⇨w→||cl (A ∙ C) (B ∙ C) (left pf) = app (⇨w→||cl A B pf) refl
⇨w→||cl (C ∙ A) (C ∙ B) (right pf) = app refl (⇨w→||cl A B pf)

⇨w→||cl* : (A B : CL) → A ⇨w B → ReflTrans _||cl_ A B
⇨w→||cl* A B pf = ||cl→||cl* A B (⇨w→||cl A B pf)

↠w→||cl* : (A B : CL) → A ↠w B → ReflTrans _||cl_ A B
↠w→||cl* A B (inj pf) = ⇨w→||cl* A B pf
↠w→||cl* A B refl = refl
↠w→||cl* A B (trans {A} {C} {B} pf pf₁) = trans (↠w→||cl* A C pf) (↠w→||cl* C B pf₁)

||cl→↠w : (A B : CL) →  A ||cl B → A ↠w B
||cl→↠w A B refl = refl
||cl→↠w (A ∙ B) (A' ∙ B') (app pf pf₁) = ↠wDoesApp A A' B B' (||cl→↠w A A' pf) (||cl→↠w B B' pf₁)
||cl→↠w (K ∙ A ∙ B) C (||K pf) = trans (inj (inj wK)) (||cl→↠w A C pf)
||cl→↠w (S ∙ A ∙ B ∙ C) (A' ∙ C' ∙ (B' ∙ C')) (||S pf pf₁ pf₂) = trans (inj (inj wS)) (↠wDoesApp (A ∙ C) (A' ∙ C') (B ∙ C) (B' ∙ C') (↠wDoesApp A A' C C' (||cl→↠w A A' pf) (||cl→↠w C C' pf₂)) (↠wDoesApp B B' C C' (||cl→↠w B B' pf₁) (||cl→↠w C C' pf₂)))

||cl*→↠w : (A B : CL) → ReflTrans _||cl_ A B → A ↠w B
||cl*→↠w A B (inj pf) = ||cl→↠w A B pf
||cl*→↠w A B refl = refl
||cl*→↠w A B (trans {A} {C} {B} pf pf₁) = trans (||cl*→↠w A C pf) (||cl*→↠w C B pf₁)

strip : (A B B' : CL) → A ||cl B → (ReflTrans _||cl_) A B' → Σ[ C ∈ CL ] ((ReflTrans _||cl_) B C) × (B' ||cl C)
strip A B B' A||clB (inj A||clB')
    with ||clDiamond A B B' A||clB A||clB'
... | (C , (B||clC , B'||clC))  = C , ((||cl→||cl* B C B||clC) , B'||clC)
strip A B A A||clB refl = B , (refl , A||clB)
strip A B B' A||clB (trans {A} {C} {B'} A||cl*C C||cl*B')
    with strip A B C A||clB A||cl*C 
... | (D , (B||cl*D , C||clD)) = D , (B||cl*D , {!   !})

||clCR : ChurchRosser (_||cl_)
||clCR A B B' (inj A||clB) A||cl*B'
    with strip A B B' A||clB A||cl*B'
... | (C , (B||cl*C , B'||clC)) = C , (B||cl*C , ||cl→||cl* B' C B'||clC)
    -- with ||clCR A B B' A||cl*B' B||cl*C
||clCR A B B' refl A||cl*B' = B' , (A||cl*B' , refl)
||clCR A B B' (trans {A} {C} {B} A||cl*C C||cl*B) A||cl*B' = {!   !}


⇨wCR : ChurchRosser (CompatCL wᴿ)
⇨wCR A B₁ B₂ A↠wB₁ A↠wB₂
    with ||clCR A B₁ B₂ (↠w→||cl* A B₁ A↠wB₁) (↠w→||cl* A B₂ A↠wB₂)
... | (C , (B₁||C , B₂||C)) = C , (||cl*→↠w B₁ C B₁||C , ||cl*→↠w B₂ C B₂||C)




-- ⇨w→ƛ↠βƛ : (A B : CL) → A ⇨w B → ＜ A ＞ƛ ↠β ＜ B ＞ƛ
-- ⇨w→ƛ↠βƛ = {!   !}

-- =w→ƛ=βƛ : (A B : CL) → A ＝w B → ＜ A ＞ƛ ＝β ＜ B ＞ƛ
-- =w→ƛ=βƛ = {!   !}


-- cl-ƛ-＝β : ∀{n} (s : Λ n) → ＜ ＜ s ＞cl ＞ƛ ＝β s
-- cl-ƛ-＝β = ?
