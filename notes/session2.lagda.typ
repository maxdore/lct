#set document(
title: [Formalising Lambda Calculus and Types]
)
#set page(numbering: "1")
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#show: init-color-my-agda

#title()

*Session 2: Substitution and rewrite relations*

Maximilian Doré, maximilian.dore\@cs.ox.ac.uk, January 2026

/* Things from the previous session that we'll need
```agda
{-# OPTIONS --allow-unsolved-metas #-}
module session2 where

open import Data.Nat as Nat using (ℕ ; zero ; suc)
open import Data.Fin as Fin using (Fin ; zero ; suc)
open import Data.Maybe as Maybe using (Maybe ; nothing ; just)
open import Data.Bool

open import session1
```
*/


== Substitution

Let us define substitution for our λ-calculus defined using De Bruijn indices.
Suppose we want to perform the following substitution (writing numbers for
variables `ν ..`):

`0 1 2 (ƛ 0 2) [ (ƛ 1 0) / 1]`

`  ↑        ↑`


The variables that we want to substitute have a `↑` underneath: in the outer
term, we want to substitute the variable `1`, in the inner term `2` refers to
the same free variable as `1` in the outer term and has to be substituted as
well. We hence have to increase the index that we are substituting by 1 if we go
inside a `ƛ`.

After substituting, one index will be unused---which is not ideal, since we want
unique representations for any term. We hence reduce all the higher variable
indices by one. More precisely, if we substitute index `j` and see a variable
`i`, we perform the following shift:

- if `i < j` then give back `i`
- if `i > j` then give back `i - 1`

We implement this as follows, where we have to wrap our result in `Maybe` since
in case `i` and `j` were equal, we don't actually care about the variable index
as we will perform the substitute in `t` in this case.

```agda
substVar : ∀{n} → Fin (suc n) → Fin (suc n) → Maybe (Fin n)
substVar zero zero = nothing
substVar {suc n} zero (suc j) = just zero
substVar {suc n} (suc i) zero = just i
substVar {suc n} (suc i) (suc j) = Maybe.map suc (substVar i j)
```


We need to take care of a second thing when we go under a `ƛ`: variables in the
term `t` that we are substituting in have to be adapted so that they still point
to the right free variables from outside. We have to be mindful however about
our shifting, since bound variables in `t` should not be changed. Our example
from above should result in the following term, where the 1 in `(ƛ 1 0)` has be
shifted to a 2 the second time we substitut in our term.

`0 (ƛ 1 0) 1 (ƛ 0 (ƛ 2 0))`

We create a function which takes in an index that tells us how many `ƛ`'s we're
inside `t`, and only shift the index if we're actually seeing a free variable.

```agda
less : ∀{n} → Fin n → Fin (suc n) → Bool
less _ zero = false
less zero (suc j) = true
less (suc i) (suc j) = less i j

lift : ∀{n} → Λ n → Fin (suc n) → Λ (suc n)
lift (ν x) bv = if less x bv then ν (Fin.inject₁ x) else ν (suc x)
lift (s ∙ t) bv = lift s bv ∙ lift t bv
lift (ƛ s) bv = ƛ (lift s (suc bv))
```

Using these helper functions it is then relatively straightforward to implement
substitution:

```agda
_[_/_] : {n : ℕ} → Λ (suc n) → Λ n → Fin (suc n) → Λ n
ν y [ t / x ] with substVar y x
... | nothing = t
... | just z = ν z
(s ∙ u) [ t / x ] = s [ t / x ] ∙ u [ t / x ]
ƛ s [ t / x ] = ƛ ( s [ lift t zero / suc x ])
```

Our substitution operation moreover computes, and we can check that our example
works.

```agda
expSubst = s [ t / suc zero ] where
  s : Λ 3
  s = ν zero ∙ ν (suc zero) ∙ ν (suc (suc zero)) ∙ (ƛ (ν zero ∙ ν (suc (suc zero))))
  t : Λ 2
  t = ƛ (ν (suc zero) ∙ ν zero)
```

You can normalise the term with `ctrl-c ctrl-n` to check that our definition
gives the expected answer. This example is of course not enough to convince
ourselves that we really defined substitution correctly---we should prove
properties about our substitution to make sure it's correct. We might do this in
the coming weeks, but let's just use substitution for now.


== Equality in λβ

We can now define our equational theory based on the β rule as follows. We use
notation close to the one in the lecture notes (note that the equality sign in
the name of the following data type is not the usual one `=`, but a unicode
version of it).

```agda
data β⊢_＝_  {n : ℕ} : Rel (Λ n) where
  refl : ∀{s} → β⊢ s ＝ s
  sym : ∀{s t} → β⊢ s ＝ t → β⊢ t ＝ s
  trans : ∀{s t u}
    → β⊢ s ＝ t → β⊢ t ＝ u → β⊢ s ＝ u
  app : ∀{s s' t t'}
    → β⊢ s ＝ s' → β⊢ t ＝ t'
    → β⊢ (s ∙ t) ＝ (s' ∙ t')
  abs : ∀{s t}
    → β⊢ s ＝ t
    → β⊢ ƛ s ＝ ƛ t
  β : ∀{s : Λ (suc n)} {t : Λ n}
    → β⊢ ((ƛ s) ∙ t) ＝ (s [ t / zero ])
```

/*
```agda
infixl -5 β⊢_＝_
```
*/

(the relation can be typed with `\beta\vdash s \= t`)



Let's try to retrace the example derivation from Lecture 2 in our system. Most
of our construction tree can be put in straightforwardly. When constructing such
proofs, it's helpful to _refine_ the goal using each step, i.e., if you start
with a hole, type in `sym` and then press `ctrl-c ctrl-r` to see if sym works as
this point, and to generate a new hole.

Note that β applied to `ƛ (ν (suc zero))` and `p` reduces to `ƛ (lift p zero)`,
as required. However, when applying the β rule to `ƛ (lift p zero) ∙ q`, we only
get an equality with `lift p zero [ q / zero ]`---it is not obvious to the
type-checker that lifting `p` with `zero` will increase all indices by one, and
thereby the substituion `q` for `zero` will not have any effect. Thus, we need
to explicity prove that such substitutions on lifted terms do not have an
effect.

We have imported the equality of Agda's standard library to use a purported
proof of this lemma. More specifically, we substitute in our equality proof into
the witness generated by `β`.

```agda
open import Relation.Binary.PropositionalEquality as Eq using (_≡_) -- unicode \==

expλβ : ∀ {n} (p q : Λ n) → β⊢ p ＝ ƛ (ƛ (ν (suc zero))) ∙ p ∙ q
expλβ p q = sym (trans (app β refl)
  (Eq.subst (β⊢ ƛ (lift p zero) ∙ q ＝_) (substLift p q zero) β))
  where
  substLift : ∀{n} → (s t : Λ n) → (i : Fin (suc n)) → (lift s i [ t / i ]) ≡ s
  substLift = {!!}
```


=== Exercise

Try to implement `substLift`. You'll need other features of propositional
equality from the standard library, in particular `Eq.cong` and `Eq.cong₂`,
which are congruence rules for `≡` for functions in one and two arguments,
respectively.
