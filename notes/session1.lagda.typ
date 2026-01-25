#set document(
title: [Formalising Lambda Calculus and Types]
)
#set page(numbering: "1")
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#show: init-color-my-agda

#title()

*Session 1: The Lambda calculus with de Bruijn indices and inductive types*

Maximilian Doré, maximilian.dore\@cs.ox.ac.uk, January 2026

/* Things from the previous session that we'll need
```agda
{-# OPTIONS --allow-unsolved-metas #-}
module session1 where
```
*/


In this term we will attempt to formalise parts of the course _Lambda Calculus
and Types_, designed by Andrew Ker and a staple of the Oxford CS curriculum. We
might sometimes deviate from the syllabus of the course, or skip some parts
which are too intricate to formalise, but will try to stay as close as possible
to the development in the lecture.

The language we use for our formalisation is Agda: https://agda.readthedocs.io/

Agda is a _theorem prover_ (or _computer proof assistant_) based on _dependent
type theory_. It is not the recommended tool if you want to formalise advanced
mathematics---Lean or Rocq are more suited for this task since they have
powerful tactics---but Agda is ideal as a logical framework to explore
different logical calculi, which is what we set out to do.

== Why formalise?

Historically, the project of putting mathematics on solid logical foundations
was born out of worries about the nature and well-foundedness of mathematics.
Today there is a community of mathematicians who want to nail down what the
_axioms_ of mathematics are, and there are even a few researchers who are
worried that a large part of the mathematical literature could be wrong.
However, most mathematicians seem to be not so worried about the soundness of
mathematics, and indeed, there have been few examples of proofs being
substantially wrong (and not just having some details or assumptions missing).

I for one think that formalising for the sake of verifying the _correctness_ of
a proof is not all that important, but leaving this as well as foundational and
philosophical questions aside, I think there are formidable pragmatic reasons
for formalising one's work.

The first one is that current theorem provers have very useful features which
will make your life easier when writing down a proof. Once we're familiar with a
theorem prover, writing out the proof formally will sometimes be faster than
writing it down with pen-and-paper, especially if the proof is quite technical
with lots of case analyses (other times, our life will be made signfificantly
harder by a theorem prover, though). And once we have formalised an argument, we
do not have to get back and check it over and over again---so while formalisation
might not increase the soundness of mathematics, it will might increase
soundness of your sleep.

Second, explaining our reasoning to a theorem prover can give us new insights
into our constructions and why they work. We have to say in very precise terms
what our definitions are, and cannot hand-wave our way through anything. We have
to logically reconstruct our informal arguments and intuitions, which will
improve our understanding of what we are formalising.

There are other reasons for why the research community should maybe move towards
formalisation (as digitising the mathematical literature makes it easier to
organise it, use machine learning for maths, etc.), but these reasons need not
concern us. I hope that the two reasons mentioned above already make it
worthwhile to learn about theorem provers.



== Getting started with Agda

Formalising, which is actually just coding, is very much not a spectator sport,
so to take most from these sessions you should get Agda running on your personal
computers. The link above has pointers to an installation guide.

It is important to _interact_ with Agda, the interactive mode has been
implemented for several popular text-editors. The most important commands are
the following (where the keyboard commands will vary if you don't use emacs).

First of all, we'll need to _load_ the file as follows:
- `ctrl-c ctrl-l`

This will then create _holes_ wherever we had put a `?` in the source code. We
can interact with holes with the following commands:

- `ctrl-c ctrl-,` prints the currrent goal type and context to another buffer.

  Putting `ctrl-u` once or twice before this changes the normalisation level of
  the proof goal, i.e., `ctrl-u ctrl-c ctrl-,` gives the unnormalised goal and
  `ctrl-u ctrl-u ctrl-c ctrl-,` the normalised goal.

- `ctrl-c ctrl-r` allows us to _refine_ the current goal using some term. This
  is particularly useful to insert a function, as Agda will create holes for any
  argument.

- `ctrl-c ctrl-c` does a case split on the given variable, which is useful for
  creating the different cases in an inductive proof.

These commands are most of what you will need to fruitfully code Agda. It might
seem a bit inconvenient at first, but once the Agda commands are in your muscle
memory it's a nice way to interact with code (I for one miss the interactive
mode when programming Haskell).

Another useful feature of the the Agda-mode is to inspect a unicode character to
find out how to type it (`M-x describe-char` in emacs).

== Inductively generated sets and dependent types in Agda

As a first approximation, we can think of Agda as a refined version of Haskell
in which the type systems has _predicates_. These predicates allow us both to
specify properties of programs, but also to express mathematical propositions
(we will see later in the course that fundamentally, program types and
mathematical propositions are the same). More concretely, a term $x$ of type $A$
can appear in another type $B space.nobreak x$, this latter type is called a _dependent type_.
The calculus underlying Agda is consequently called _dependent type theory_.

Let us start our development with a non-dependent type, however: the natural
numbers:

/*
We will use the definitions of natural numbers and finite types from the library later.
```agda
module forgetlater where
```
*/

```agda
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
```

This definition is similar to how one we could define the natural numbers in,
e.g., Haskell, just with some syntactic differences (in fact, the students which
have done _Functional Programming_ in Oxford will have defined such a `Nat`
datatype in their tutorial sheets). Note that the type `ℕ` is called a `Set` in
Agda, and it does indeed behave very similarly to the sets that we have
generated with inference rules in the lectures. In particular, we can derive the
induction principle for these natural numbers.

```agda
  indℕ : {P : ℕ → Set}
    → P zero
    → ((n : ℕ) → P n → P (suc n))
    -------------------------------------
    → (n : ℕ) → P n
  indℕ base step zero = base
  indℕ base step (suc n) = step n (indℕ base step n)
```

The type `P` above is a type depending on the natural numbers, it is hence a
_property_ of the natural numbers. To show that `P` holds for any natural
number, we have to show that `P` holds for `zero`---the base case of our
induction---and that for any number `n`, provided that `P n` holds, then also `P
(suc n)` must hold---the inductive step. This induction principle can be
established by pattern matching on the given natural number. Note how the
program is exactly the same as the `fold` for a `Nat` datatype in Haskell (this
is why `fold`s for Algebraic Data Types are sometimes called _induction
principles_). Pattern matching utilises that with an inductive type we really
mean the _least set_ generated by its constructor rules.

Let us define our first dependent type, namely finite type with `n` elements.

```agda
  data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (suc n)
    suc  : {n : ℕ} (i : Fin n) → Fin (suc n)
```

The first constructor says that `zero` is an element of any `Fin n` as long as
`n` is greater than `zero`. The second construtor says that if we know that `i`
is in `Fin n`, then the successor of `i` is in `Fin (suc n)`. Intuitively, `Fin n`
has $n - 1$ elements `zero`, `suc zero`, ..., and can be thought of as the
set $\{0, ... , n-1\}$.

This type doesn't seem particularly exciting, but it is in fact a very powerful
type since the `n` does not have to be a fixed natural number, but can be a
complex function term with free variables, i.e., `n` can be an arbitrary program
producing something of type `ℕ`. For example, we can consider for an arbitrary
`n` the finite type of elements which have on element more, i.e., `Fin (suc n)`.
The fact that programs can appear in types makes dependent type theory very
powerful and expressive (but also difficult as a type theory---to have some
notion of equality between types, we need to deal with equalities between
programs).


== The Lambda Calculus

We have described terms of the lambda calculus using an inductive definition in
the lectures, and we will be able to use inductive types to much the same effect
in Agda. We will completely side-step the issue of $alpha$-equivalence by using
de Brujin indices for bound variables. While it's also possible formalise a
λ-calculus with explicit variable names, setting it up properly requires quite
some care and complicates our proofs, so we will stick with a name-free
representation for now.

We use the power of dependent types to specify which variables are free in a
given term, where the idea is that `Λ n` may contain the free variables $\{0,
... , n-1 \}$.

/*
```agda
open import Data.Nat hiding (compare ; _<_)
open import Data.Nat.Properties
open import Data.Fin hiding (_+_ ; _>_)
```
*/


```agda
data Λ (n : ℕ) : Set where
  ν : Fin n → Λ n
  _∙_ : (s t : Λ n) → Λ n
  ƛ : Λ (suc n) → Λ n
```

/*
```agda
infixl 14 ν
infixl 12 ƛ
infixl 10 _∙_
```
*/

(The unicode characters of the different constructors can be typed with
`\nu`, `\.` and `\Gl-`)

The constructor `ν` can be used for any element in $\{0, ... n -1\}$ to
construct a variable in `Λ n`. Application just takes two terms with the same
set of free variables (we can promote any term using $n$ free variables to one
in $m$ variables provided that $m$ is larger than $n$, which is a useful
exercise to prove). Abstraction _binds_ a variable, we hence have one free
variable binding a term with `ƛ`. By convention, we assume that the 0-th
variable is bound by this `ƛ`.

`Λ 0` corresponds to the closed terms. For example, we can define standard
combinators as follows.
```agda
tK fK : Λ 0
tK = ƛ (ƛ (ν (suc zero)))
fK = ƛ (ƛ (ν zero))

```


We refer to free variables by going beyond the binders, i.e, the term $lambda x
y.y z$ has one free variable $z$, we hence refer to $z$ with 2 if we're two
λ's in.

```agda
exp₁ : Λ 1
exp₁ = ƛ (ƛ (ν zero ∙ ν (suc (suc zero))))
```

We can define both functions and prove properties by pattern matching on `Λ n`.
For example, we can define a function which counts the number of variables like
this.

```agda
numvars : ∀{n} → Λ n → ℕ
numvars (ν x) = 1
numvars (s ∙ t) = numvars s + numvars t
numvars (ƛ s) = numvars s
```


Properties of $lambda$ terms are just dependent types, such as the 
type `numvars s > 0` which depends on the term `s`. The relation `_>_` is imported
from Agda's standard library, and this library also contains some lemmas that we
can use to prove that any term must contain at least one variable.

```agda
atleastonevar : ∀{n} → (s : Λ n) → numvars s > 0
atleastonevar {n} (ν x) = s≤s z≤n
atleastonevar {n} (s ∙ t) = <-≤-trans (atleastonevar s) (m≤m+n (numvars s) (numvars t))
atleastonevar {n} (ƛ s) = atleastonevar s
```

We can hence understand the function type in Agda as a $forall$-quantifier: for
all terms `s`, some property of `s` holds. In dependent type theory, function
types are called $Pi$ types, $Pi$ is hence the $forall$ for programmers.


== Equational Theory

We can define all sorts of 'sets' using inductive types, in particular also
relations. In type theory, a binary relation $R$ on $A$ is not a set of pairs of
$A$, but instead a function which maps two copies of $A$ to a `Set`.
Intuitively, $R space.nobreak x space.nobreak y$ for two $x space.nobreak y : A$
is the set of all the _proofs_ that $x$ and $y$ are related (this already hints
at the fact that we are not really, constructing inductive _sets_ in type
theory, but this is for a later discussion. The fact that `Rel` lives in `Set₁`
is to avoid what is called _impredicativity_, which is also something that we
might discuss later.)

```agda
Rel : Set → Set₁
Rel A = A → A → Set
```

Using this notion of relation we can neatly retrace our definition for the
equational theory of $lambda beta$ (where the lines beginning with `--` are just
comments to make the constructors look like inferences rules).

```agda
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
```

/*
```agda
infixl -5 _β=_
```
*/


In the definition of `β`, we have left a hole---we need to define our
substitution operation to say what `(ƛ s) ∙ t` equals to. Note that $s$ has one
free variable more than $t$ above, and that our substitution needs to yield a
term which has as many free variables as $t$.


== Exercises

=== 1.

Try to define substitution for our terms.

```agda
_[_/_] : {n : ℕ} → Λ (suc n) → Λ n → Fin (suc n) → Λ n
s [ t / x ] = {!!}
```

You might want to define a helper function which implements what needs to happen
if $s$ is a variable. The `with` construct in Agda will be helpful for doing
pattern matching on the result of this helper function:
https://agda.readthedocs.io/en/latest/language/with-abstraction.html

You can import all sorts of datatypes from the standard-library, e.g., `Maybe`
may be useful. For this you need to `open import Data.Maybe`.

=== 2.

Try to prove the derivation in $lambda beta$ that was done in Lecture 2, i.e.,
give a proof of the following:

```agda
expλβ : ∀ {n} {p q : Λ n} → p β= ƛ (ƛ (ν (suc zero))) ∙ p ∙ q
expλβ = {!!}
```

What auxiliary lemmas about substitution do we need?
