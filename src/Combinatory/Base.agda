module Combinatory.Base where

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


data CL : Set where
    ν : ℕ → CL
    K : CL
    S : CL
    _∙_ : CL → CL → CL

infixl 14 ν
infixl 10 _∙_

_[_/_]cl : CL → CL → ℕ → CL
ν x₁ [ B / x ]cl with x₁ == x
... | true = B
... | false = ν (x₁ ∸ 1)
K [ B / x ]cl = K
S [ B / x ]cl = S
(A ∙ C) [ B / x ]cl = (A [ B / x ]cl) ∙ (C [ B / x ]cl)

data CL⊢_＝_ : Rel CL where
    refl : ∀{A} → CL⊢ A ＝ A
    sym : ∀{A B} → CL⊢ A ＝ B → CL⊢ B ＝ A
    trans : ∀{A B C} → CL⊢ A ＝ B → CL⊢ B ＝ C → CL⊢ A ＝ C
    app : ∀{A A' B B'} → CL⊢ A ＝ A' → CL⊢ B ＝ B' → CL⊢ (A ∙ B) ＝ (A' ∙ B')
    Krule : ∀{A B} → CL⊢ (K ∙ A ∙ B) ＝ A
    Srule : ∀{A B C} → CL⊢ (S ∙ A ∙ B ∙ C) ＝ (A ∙ C ∙ (B ∙ C))

data CompatCL (R : Rel CL) : Rel CL where
  inj : ∀{A B}
    → R A B
    → CompatCL R A B
  left : ∀{A B C}
    → CompatCL R A B
    → CompatCL R (A ∙ C) (B ∙ C)
  right : ∀{A B C}
    → CompatCL R A B
    → CompatCL R (C ∙ A) (C ∙ B)

data wᴿ : Rel CL where
  wK : ∀{A B}
    → wᴿ (K ∙ A ∙ B) A
  
  wS : ∀{A B C}
    → wᴿ (S ∙ A ∙ B ∙ C) (A ∙ C ∙ (B ∙ C))

module _ where
  _⇨w_ = CompatCL wᴿ
  _↠w_ = ReflTrans (CompatCL wᴿ)
  _＝w_ = ReflTransSym (CompatCL wᴿ)

-- theorem about all closed normal forms?

iterateLift : ∀{n} → Λ n → (m : ℕ) → Λ (m + n)
iterateLift {n} s zero = s
iterateLift s (suc m) = lift (iterateLift s m) zero

-- idea: get max FV
numFVs : CL → ℕ
numFVs (ν x) = suc x
numFVs K = 0
numFVs S = 0
numFVs (A ∙ B) = (numFVs A) ⊔′ (numFVs B)

postulate
  ＜_＞ƛ : (cl : CL) → Λ (numFVs cl)
-- ＜ ν x ＞ƛ = ν (fromℕ x)
-- ＜ K ＞ƛ = 𝕜
-- ＜ S ＞ƛ = 𝕤
-- ＜ A ∙ B ＞ƛ with (numFVs A) < (numFVs B)
-- ... | true = {!  (iterateLift (＜ A ＞ƛ) (numFVs B ∸ numFVs A)) ∙ ＜ B ＞ƛ !}
-- ... | false = {!  ＜ A ＞ƛ ∙ (iterateLift (＜ B ＞ƛ) (numFVs A ∸ numFVs B)) !}

hasZero : CL → Bool.Bool
hasZero (ν x) = x == zero
hasZero K = false
hasZero S = false
hasZero (A ∙ B) = (hasZero A) ∨ (hasZero B)

drop : CL → CL
drop (ν zero) = ν zero
drop (ν (suc x)) = ν x
drop K = K
drop S = S
drop (A ∙ A₁) = (drop A) ∙ (drop A₁)

ƛƛ : CL → CL
ƛƛ (ν zero) = S ∙ K ∙ K
ƛƛ (ν (suc x)) = K ∙ ν x
ƛƛ K = K ∙ K
ƛƛ S = K ∙ S
ƛƛ (A ∙ B) with hasZero (A ∙ B)
... | true = S ∙ (ƛƛ A) ∙ (ƛƛ B)
... | false = K ∙ drop (A ∙ B)

＜_＞cl : ∀{n} → Λ n → CL
＜ ν x ＞cl = ν (toℕ x)
＜ s ∙ t ＞cl = ＜ s ＞cl ∙ ＜ t ＞cl
＜ ƛ s ＞cl = ƛƛ (＜ s ＞cl)
