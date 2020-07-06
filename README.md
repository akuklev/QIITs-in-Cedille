Intensional Identity Type and Quotient Inductive-Inductive Types in Core Cedille
================================================================================

In their article [1] Abel et al. note that Leibniz Equality is morally the impredicative “Church-”encoding for Martin-Löf Identity type of Intuitionistic Type Theories. Core Cedille[2, 3, 4] is a novel logically consistent typed lambda calculus (i.e. no first-class inductive types, everything is made of lambda terms) with a unique long sought-after property: W-types (basic inductive types available in Intuitionistic Type Theories, such as natural numbers, lists, trees, etc.) can be encoded within the calculus with correct recursion and induction principles. It is tempting to try to encode the identity type and ultimately the vast range of Quotient Inductive-Inductive Type Families (QIITs) including the type of Cauchy Reals and initial algebras for all finitary Generalised Algebraic Theories without equations on sorts.

It is worth noting, that expressivity of Core Cedille comparable to Intensional Type Theories and even Predicative Calculus of Cumulative Inductive Constructions (pCuIC), the state-of-the art basis of the Coq proof assistant, where Yoneda lemma can be proven. In comparison to them, Core Cedille lacks universes and large elimination, but enjoys first-class support for large categories and similar properly large constructions. It is hoped for, it is possible to combine advantages of both worlds in a manner akin to ZMC/S set theory: proper support for largness and a strong reflection property that for every large construction there is a univalent universe large enough to contain a faithful model of that structure (applying the reflection principle to itself yields an unbounded hierarchy of universes both upwards and downwards), see https://golem.ph.utexas.edu/category/2009/11/feferman_set_theory.html.


§ Preliminaries: Notation and the Type System
---------------------------------------------

We'll work in a system where terms don't in general have a canonical type, but can be typechecked against a given type, possibly nonunique. Types are generally written in title-case (e.g. `Nat` for natural numbers, `Int` for integer numbers) and can have parameters (e.g. `List[Nat]` for list of natural numbers or `FList[Int, 5]` for list of integer numers of length 5). We'll write bare (untyped) lambda terms like
```
\x ↦ expr(x)
```

and lambda terms with typed variables like
```
(\x : Nat) ↦ expr(x)
```

If two lambda terms `f` and `g` are identical as bare terms (i.e. with eventual type annotations stripped), we'll write `f ⩦ g`. To give an example, `(\x : Nat) ↦ x` and `(\x : AnyOtherType) ↦ x` are identical as bare terms. For nested lambda terms like
```
(\n : Nat) ↦  (\m : Nat) ↦ (q : Int) ↦ ...
```
we'll sometimes use an equivalent shorter notation
```
(\n \m : Nat, \q : Int) ↦ ...
```

A typed lambda term can be checked against it type: if for a term `f := (\x : X) ↦ expr(x)` the term `expr(x)` typechecks against type `Y`, the term `f` typechecks against `X -> Y`. Such types are called function types. In general, the type `Y` can be dependent on the variable `x`: consider a function `f(n : Nat)`, generating some list of integers of length `n`, say first `n` Fibonacci numbers, than each `f(n)` whould typecheck against `FList[Int, n]`, in this case can write the type of `f` as
```
(\n : Nat) -> FList[Int, n]
```
Such types are called dependent function types. Note the notational difference between lambda terms and dependent function types: `↦` vs `->`.

Now consider the case you have a function on lists that preserves list length, and you want to express this property in its type. For this, you need a new kind of type, it will be written
```
∀\n : Nat, FList[X, n] -> FList[Y, n]
```
An annotated function checkable against this type will have an aditional parameter `\n : Nat` to provide the type annotation for its argument. The parameter is very much like argument, but it can be used only in type annotations, not in the body of the function, for this reason we'll introduce the following notation:
```
(0 \n : Nat) ↦ (l : FList[X, n]) ↦ ...
```
or equivalently
```(0 \n : Nat, l : FList[X, n]) ↦ ...
```

Zero before the variable means, it is allowed to be used in the body exactly zero times. (The notation suggests, that besides notation for arguments and parameters, there can also be a notation for resources `(1 \x : MutuallyExclusiveResource)`, variables that have to be used exactly once.) Parameters can be used to require some additional preconditions on arguments, and can be used to establish some postconditions on computed value.

Parameters' types are allowed to contain a special symbol `﹡` standing for “any type”, which is disallowed for arguments. In particular, we have can define the function
```
id := (0 \T : ﹡, \x : T) ↦ x
```
of the type 
```
∀\T : ﹡, T -> T
```
Note that `id ⩦ (\x ↦ x)`.

Note that `Nat -> ﹡` (sequence of types), `﹡ -> ﹡` (type parametrized by type) or even `(Nat -> ﹡) -> ﹡ -> ﹡` (type parametrized by a type and a sequence of types) are also valid types for parameters, but never for arguments.

Both lambda expressions and types can be applied to arguments (written by juxtaposition `f x` or with parentheses `f(x)`) and parameters (written like `id[Nat]`, `List[Nat]` or `FList[Int, n]`)

§ Encoding Nat in Core Cedille
------------------------------

Church numerals are terms of the following form:
```
zero := (0 \T : ﹡, step : T -> T, base : T) ↦ base
once := (0 \T : ﹡, step : T -> T, base : T) ↦ step(base)
twice := (0 \T : ﹡, step : T -> T, base : T) ↦ step(step(base))
thrice := (0 \T : ﹡, step : T -> T, base : T) ↦ step(step(step(base)))
```

If a number `n` is given in form of a Church numeral, any function can be iterated `n` times simply by applying `n` to that function:
```
(twice f)(x) = f(f(x))
```

Church numerals could be called “function iterators”. We can easily write down the type of Church numerals
```
Natᶜ := ∀\T : ﹡, (T -> T) -> T -> T
```
and the successor function
```
succ(\n : Natᶜ) := (0 \T : ﹡, step : T -> T, base : T) ↦ (n[T] step)(step(base))
```

Church numerals can only iterate functions returning values of the same type as their arguments, i.e. functions of the type `∀\T : ﹡, (T -> T)`. Can we possibly iterate a function of a more general type? That's precisely what happens when we perform mathematical induction or Nat-induction: given a predicate `P : Nat -> ﹡` it constructs a proff of `P[n]`  for arbitrary `n : Nat` given a proof of induction step `step : P(n) -> P(succ n)` and of the base case `base P(zero)`:
```
Natᴵ(\n : Natᶜ) := ∀\T : (Natᶜ -> ﹡), (step: ∀\m : Nat, T[m] -> T[succ m]) -> (base : T[zero]) -> T[n]
```


The crucial feature of Core Cedille is the dependent intersection type (first introduced by A. Kopylov) that allows to define the type
```
Nat := (\n : Natᶜ, n : Natᴵ(n))
```
Inhabitants of this types are Church numerals (“function iterators”) `\n` that simultaneously typecheck as induction proofs (“dependent function iterators”) for themselves. Fortunatelly, for each Church numeral `n` as written above we can write down an induction proof `n'` and it turns out `n ⩦ n'`, thus Church numerals inhabit the type `Nat`. Similar construction can be carried out for any W-type[3] yielding an impredicative encoding with correct dependent elimination principle.

§ Leibniz equality and Id-types
-------------------------------
