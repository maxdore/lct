module Combinatory.LambdaLambdaDoesLambda where

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

noZero→noSubst : (A B : CL) → hasZero A ≡ false → CL⊢ drop A ＝ (A [ B / 0 ]cl)
noZero→noSubst (ν (suc x)) B pf = refl
noZero→noSubst K B pf = refl
noZero→noSubst S B pf = refl
noZero→noSubst (A ∙ C) B pf with hasZero A in AhasZero
noZero→noSubst (A ∙ C) B pf | false = app (noZero→noSubst A B AhasZero) (noZero→noSubst C B pf)

lambdaDoesLambdaInCL : (A B : CL) → CL⊢ (ƛƛ A) ∙ B ＝ (A [ B / zero ]cl)
lambdaDoesLambdaInCL (ν zero) B = trans Srule Krule
lambdaDoesLambdaInCL (ν (suc x)) B = Krule
lambdaDoesLambdaInCL K B = Krule
lambdaDoesLambdaInCL S B = Krule
lambdaDoesLambdaInCL (A ∙ C) B with hasZero A in AhasZero
lambdaDoesLambdaInCL (A ∙ C) B | true = trans Srule (app (lambdaDoesLambdaInCL A B) (lambdaDoesLambdaInCL C B))
lambdaDoesLambdaInCL (A ∙ C) B | false with hasZero C in ChasZero
lambdaDoesLambdaInCL (A ∙ C) B | false | true = trans Srule (app (lambdaDoesLambdaInCL A B) (lambdaDoesLambdaInCL C B))
lambdaDoesLambdaInCL (A ∙ C) B | false | false = trans Krule (app (noZero→noSubst A B AhasZero) (noZero→noSubst C B ChasZero))

-- lambdaDoesLambdaInbeta : (A : CL) → β⊢ (＜ ƛƛ A ＞ƛ) ＝ (ƛ (＜ A ＞ƛ))
-- lambdaDoesLambdaInbeta = ?