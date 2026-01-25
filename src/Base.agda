module Base where

open import Data.Nat
open import Data.Fin


data Λ (n : ℕ) : Set where
  ν : Fin n → Λ n
  _∙_ : (s t : Λ n) → Λ n
  ƛ : Λ (suc n) → Λ n


infixl 14 ν
infixl 12 ƛ
infixl 10 _∙_


tK fK : Λ 0
tK = ƛ (ƛ (ν (suc zero)))
fK = ƛ (ƛ (ν zero))


Rel : Set → Set₁
Rel A = A → A → Set


data _β=_ {n : ℕ} : Rel (Λ n) where
  refl : ∀{s}
    ----------------------------------------
    → s β= s

  sym : ∀{s t}
    → s β= t
    ----------------------------------------
    → t β= s

  trans : ∀{s t u}
    → s β= t
    → t β= u
    ----------------------------------------
    → s β= u

  app : ∀{s s' t t'}
    → s β= s' → t β= t'
    ----------------------------------------
    → (s ∙ t) β= (s' ∙ t')

  abs : ∀{s t}
    → s β= t
    ----------------------------------------
    → ƛ s β= ƛ t

  β : ∀{s : Λ (suc n)} {t : Λ n}
    ----------------------------------------
    → ((ƛ s) ∙ t) β= {!!}


infixl -5 _β=_



_[_/_] : {n : ℕ} → Λ (suc n) → Λ n → Fin (suc n) → Λ n
s [ t / x ] = {!!}

expλβ : ∀ {n} {p q : Λ n} → p β= ƛ (ƛ (ν (suc zero))) ∙ p ∙ q
expλβ = {!!}
