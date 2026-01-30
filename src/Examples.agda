module Examples where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)

open import Base


tK fK : Λ 0
tK = ƛ (ƛ (ν (suc zero)))
fK = ƛ (ƛ (ν zero))


expSubst = s [ t / suc zero ] where
  s : Λ 3
  s = ν zero ∙ ν (suc zero) ∙ ν (suc (suc zero)) ∙ (ƛ (ν zero ∙ ν (suc (suc zero))))
  t : Λ 2
  t = ƛ (ν (suc zero) ∙ ν zero)

