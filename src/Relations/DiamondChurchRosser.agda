module Relations.DiamondChurchRosser where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Product

open import Base
open import Relations.Base

Diamond→CR : ∀{A} → (R : Rel A) → Diamond R → ChurchRosser R
Diamond→CR = {!!}
