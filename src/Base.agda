module Base where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Maybe as Maybe using (Maybe ; nothing ; just)
open import Data.Bool

data Λ (n : ℕ) : Set where
  ν : Fin n → Λ n
  _∙_ : (s t : Λ n) → Λ n
  ƛ : Λ (suc n) → Λ n

infixl 14 ν
infixl 12 ƛ
infixl 10 _∙_

substVar : ∀{n} → Fin (suc n) → Fin (suc n) → Maybe (Fin n)
substVar zero zero = nothing
substVar {suc n} zero (suc j) = just zero
substVar {suc n} (suc i) zero = just i
substVar {suc n} (suc i) (suc j) = Maybe.map suc (substVar i j)

less : ∀{n} → Fin n → Fin (suc n) → Bool
less _ zero = false
less zero (suc j) = true
less (suc i) (suc j) = less i j

lift : ∀{n} → Λ n → Fin (suc n) → Λ (suc n)
lift (ν x) bv = if less x bv then ν (Fin.inject₁ x) else ν (suc x)
lift (s ∙ t) bv = lift s bv ∙ lift t bv
lift (ƛ s) bv = ƛ (lift s (suc bv))

_[_/_] : {n : ℕ} → Λ (suc n) → Λ n → Fin (suc n) → Λ n
ν y [ t / x ] with substVar y x
... | nothing = t
... | just z = ν z
(s ∙ u) [ t / x ] = s [ t / x ] ∙ u [ t / x ]
ƛ s [ t / x ] = ƛ ( s [ lift t zero / suc x ])

