module Relations.BetaRedImpl where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)

open import Base
open import Relations.Base
open import Relations.LambdaBeta
open import Relations.BetaRed



β⊢＝→＝β : ∀{n} (s t : Λ n) → β⊢ s ＝ t → s ＝β t
β⊢＝→＝β = {!!}
＝β→β⊢＝ : ∀{n} (s t : Λ n) → s ＝β t → β⊢ s ＝ t
＝β→β⊢＝ = {!!}
