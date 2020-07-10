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

If two lambda terms `f` and `g` are identical as bare terms (i.e. with eventual type annotations stripped), we'll write `f ⩦ g`. To give an example, `(\x : Nat) ↦ x` and `(\x : AnyOtherType) ↦ x` are identical as bare terms.

For nested lambda terms like
```
(\n : Nat) ↦  (\m : Nat) ↦ (q : Int) ↦ ...
```
we'll sometimes use an equivalent shorter notation
```
(\n \m : Nat, \q : Int) ↦ ...
```
(NB: Backslash before variable name should be seen as freshness sigil: it belongs to the variable name and is used exactly once with each variable: at the point where its name appears the first time. Freshness sigils are mainly useful in languages with pattern matching, where patterns can contain both placeholders (labeled by fresh variable names) for reading values out and interpopations (labeled by names of constants or variables already in scope) for filling the values in.)

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
```
(0 \n : Nat, l : FList[X, n]) ↦ ...
```

Zero before the variable means, it is allowed to be used in the body exactly zero times. (The notation is borrowed from the Idris 2 language: Besides arguments that can be used multiple times and parameters that are not allowed to be used in function body, Idris also supports resources `(1 \x : MutuallyExclusiveResource)`, variables that have to be used exactly once.) Parameters can be used to require some additional preconditions on arguments, and can be used to establish some postconditions on computed value.

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

Church numerals can only iterate functions returning values of the same type as their arguments, i.e. functions `f` of the type `∀\T : ﹡, (T -> T)`. Can we possibly iterate a function of a more general type? Yes, theoretically type `T` could be indexed over some type `I`, and its index could change every time we apply the function `f`. Let's call the index updating function `g` and write down signatures of `f` and `f'`:
```
g : I -> I
T : I -> ﹡
f : ∀\i : I, T[i] -> T[g i]
```

It would be desirable if we could iterate such functions as well: for each Church numeral (“iterator”) `n` we want to have a “dependent iterator” `n'` acting on such `f`s in so that
```
(n' f) : ∀\i : I, T[i] -> T[(n g) i]
```

Unfortunately, it cannot work exactly this way, because there is no `g` on the left side here (it is not encoded into `f` and there is no way for universal generalized iterator `n'` to guess it), so we have to fine-tune the setup. For the purpose of iterating `f` we're not interested in all values of index `i : I`, but only values obtained by iterated application of `g` to the base value (the index `i : I` of the type `T[i]` where the argument `x : T[i]` of `f(x)` and `(n' f)(x)` lives), so we can retype `f`: let `T'[zero] := T[i]` be the type where the argument lives and `T'[n] := (n g) i`, then
```
f' : ∀\n : Nat, T[n] -> T[succ n]
```
And now we can write
```
(n' f') : T[0] -> T[n]
```
Now how does the type of dependent iterator `n' : Natᴵ(n)` (it obviously depends on `n` itself) look like?

Under propositions-as-types interpretation of types `Natᴵ(n)` is precisely the statement we can perform mathematical induction (Nat-induction) up to `n`: given a predicate `T : Nat -> ﹡`, an induction step `step : T[n] -> T[succ n]` and the base case `base : T[zero]`, we obtain `T[n]` for arbitrary `n : Nat`:
```
Natᴵ(\n : Natᶜ) := ∀\T : (Natᶜ -> ﹡), (step: ∀\m : Natᶜ, T[m] -> T[succ m]) -> (base : T[zero]) -> T[n]
```

It turns out, we can actually easily provide typed lambda terms `zero' : Natᴵ(zero)`, `once' : Natᴵ(once)`, etc. Moreover they coincide with respective Church numerals as bare terms: `n ⩦ n'`.

The crucial feature of Core Cedille is the dependent intersection type (first introduced by A. Kopylov) that allows to define the type
```
Nat := (\n : Natᶜ, n : Natᴵ(n))
```
Inhabitants of this type are Church numerals (“simple iterators”) `n` that simultaneously typecheck as “dependent iterators” for themselves. Since the definition of the type `Natᴵ(\n : Natᶜ)` contains this small `ᶜ` above for its arguments, there might be a problem. But fortunatelly, it turns out in Cedille, that these `ᶜ`s can be lifted: each `n : Nat` typechecks as its own dependent eliminator:
```
n : ∀\T : (Natᶜ -> ﹡), (step: ∀\m : Natᶜ, T[m] -> T[succ m]) -> (base : T[zero]) -> T[n]
```

Thus, `Nat` turns out to be the completely faithful representation of the W-type of natural numbers: it satisfies `Nat-`induction in the strong computational sense. Note that the type `Natᶜ` is not yet that good: It is well known that in Calculus of Constructions (essentially, Core Cedille without dependent intersection types) one cannot derive the induction principle for the type `Natᶜ`, moreover there are reasonable models of Calculus of Constructions where the type `Natᶜ` contains a kind of fixpoint operators on some `T -> T` functions in addition to Church encodings of natural numbers. The dependent intersection rules out these “non-standard” (or rather “not-in-general-computable”) iterators.

Similar construction can be carried out for any W-type[3] yielding an impredicative encoding with correct dependent elimination principle.


§ Leibniz Equality and Id-types
-------------------------------

Leibniz Equality is the principle that two things `\x \y : T` are called equal iff for any predicate `P : T -> ﹡` the proposition `P[x]` implies `P[y]`, if any statement about `x` is true, than so is the same statement about `y`. Leibniz equality principle defines equal as indiscernible. Under propositions-as-types interpretation, this principle can be reified as the following type:  
```
Eq[\T : ﹡](\x \y : T) := ∀\P : (T -> ﹡), P[x] -> P[y]
```

We can easily provide a term stating every `x` is equal to itself:
```
refl[\T : ﹡](\x : T) := (0 P : T -> ﹡, e : P[x]) ↦ e
```
This property of equality is called reflexivity. Symmetry and transitivity for `Eq` can be also easily proved.

For structured objects (amongst other things, geometric structures such as graphs, and algebraic structures, such as groups, rings, etc.) it makes sense to talk about identifiablity instead of equality. An identification `p : Idᵀ(G, H)` between two objects `G` and `H` (called isomorphism in case of algebraic structures) is a rule allowing to “transport” any construction `f(\x : G)` on `G` and any true statement `P[G]` about `G` into a construction on `H`/true statement `P[H]` about `H` and vice versa. By transporting true statements both ways, the notion of identifiability subsumes the notion of indiscernibility (“Leibniz equality”), but it extends it by acknowledging that there can be more than one way to identify things, and the choice of identification is substantial. (The recent insight, that identifications themselves are structured mathematical objects in their own right, and it makes a lot of sense to think about identifications between identifications, lead to a novel research area called Homotopy Type Theory.)

The type of identifications `p : Idᵀ(G, H)` can be defined in Intuitionistic Type Theories as an indexed inductive type, but it is not a W-type. Its defining features are the only constructor `refl[\T : ﹡](\x : T) : Idᵀ(G, H)` and the “induction principle” known as the J-rule:
```
J[\T : ﹡](\x \y : T, p : Idᵀ(x, y)) := ∀\P : (\a \b : T -> Idᵀ(a, b) -> ﹡), ((t : T) -> P[t, t, refl]) -> P[x, y, p]
```

Now let's try to apply the approach we already employed for W-types to construct the `Id`-type from `Eq` in Core Cedille:
```
Id[\T : ﹡](\x \y : T) := (\p : Eq[T](x, y), p : ∀\P : (\a \b : T -> Eq[T](a, b) -> ﹡), ((\t : T) -> P[t, t, refl]) -> P[x, y, p])
```

{Here comes a coding experiment to define this type in Cedille and ensuring it satisfies induction principle for itself.}

<!---
§ Impredicative Encoding for Int as Quotient Inductive Type
-----------------------------------------------------------

```
Intᶜ := ∀\T : ﹡, (step : T -> T) -> (unstep : T -> T) ->
 (e1 : ∀\x : T, Eq[T](x, step(unstep(x)))) ->
 (e2 : ∀\x : T, Eq[T](x, unstep(step(x))))
 -> T -> T
```

--->
