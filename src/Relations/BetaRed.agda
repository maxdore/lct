module Relations.BetaRed where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)

open import Base
open import Relations.Base


data βᴿ : RelΛ where
  β : ∀{n}{s : Λ (suc n)} {t : Λ n}
    → βᴿ ((ƛ s) ∙ t)  (s [ t / zero ])

module _ {n : ℕ} where
  open ReflTransSym
  open Compat
  _⇨β_ = Compat βᴿ
  _↠β_ = ReflTrans (Compat βᴿ {n})
  _＝β_ = ReflTransSym (Compat βᴿ {n})
