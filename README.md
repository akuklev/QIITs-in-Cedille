Core Cedille has Id-Types and QIITs
===================================

In their article [1] Abel et al. note that Leibniz Equality is morally the impredicative “Church-”encoding for Martin-Löf Identity type of Intuitionistic Type Theories. Core Cedille[2, 3, 4] is a novel logically consistent typed lambda calculus (i.e. no first-class inductive types, everything is made of lambda terms): with an extraordinary and long sought-after property: W-types (basic inductive types available in Intuitionistic Type Theories, such as natural numbers, lists, trees, etc.) and dependently-typed pairs can be encoded within the calculus with correct recursion and induction principles. Since the calculus also readily includes dependently-typed functions, it is fair to say that Core Cecille is known to subsume basic Intuitionistic Type Theory except for universes and identity types.

In present work we show how to encode the identity type, and ultimately also Quotient Inductive-Inductive Type Families (QIITs) including the type of Cauchy Reals and initial algebras for all finitary Generalised Algebraic Theories without equations on sorts. Thus, Core Cedille subsumes a version of Homotopy Type Theory lacking only universes and large elimination, but supporting first class complex-kinded polymorphism instead[^1]. 

_______
[^1]: As opposed to Intuitionistic Type Theories where one can only talk about `U`-small categories for a given universe `U`, the language of Core Cedille allows to talk about categories and other structures without size restrictions. We hope that it is possible to combine advantages of both worlds in a manner akin to ZMC/S set theory: namely by a strong reflection property ensuring there is a univalent universe `U`, so that any definable type can be relativised into it, and construction internal to `U` but not explicitly using it can be generalised out of it, e.g. any proof in the category of `U`-small groups, that doesn't use smallness explicitly, should automatically generalise a proof about groups without any size restrictions. Applying the reflection principle to itself yields a hierarchy of universes unbounded both upwards and downwards. For an extensive discussion of ZMC/S as a particularly pleasing foundation for category theory see https://golem.ph.utexas.edu/category/2009/11/feferman_set_theory.html.


§ Preliminaries: Notation and the Type System
---------------------------------------------

(Our rather unorthodox notation is inspired by Conor McBrides Quantitative Type Theories)

We'll write bare, untyped lambda terms like this (but we'll actually never write them):
```
\x ↦ expr(x)
```

There are data types, like `Int` standing for “integer number” or `Nat` standing for “natural number”, they are used to write down annotated lambda terms like this:
```
(\x : Nat) ↦ expr(x)
```

The thing to the right of the colon has to be a datatype. Types are generally written in title-case (e.g. `Nat` for natural numbers, `Int` for integer numbers) and can have parameters (e.g. `List[Nat]` for list of natural numbers or `FList[Int, 5]` for list of integer numers of length 5). Not all types are datatypes: for example there is a type `﹡` of all datatypes. In type definitions, the thing to the right of the colon may by any type, non neccessarily a datatype. For example, the definition of `FList` begins as follows:
```
FList[\T : ﹡, length : Nat] := ...
```

For nested lambda terms like
```
(\n : Nat) ↦ (\m : Nat) ↦ (q : Int) ↦ ...
```
we'll sometimes use an equivalent shorter notation
```
(\n \m : Nat, \q : Int) ↦ ...
```
(NB: Backslash before variable name should be seen as freshness sigil: it belongs to the variable name and is used exactly once with each variable: at the point where its name appears the first time. Freshness sigils are mainly useful in languages with pattern matching, where patterns can contain both placeholders (labeled by fresh variable names) for reading values out and interpopations (labeled by names of constants or variables already in scope) for filling the values in.)

We'll work in a system where terms don't in general have a canonical type, but can be typechecked against a given type, possibly nonunique. In particular, if for a term `f := (\x : X) ↦ expr(x)` the term `expr(x)` typechecks against type `Y` for every `x : X`, the term `f` typechecks against `X -> Y`. Such types are called function types. In general, the type `Y` can be dependent on the variable `x`: consider a function `f(n : Nat)`, generating some list of integers of length `n`, say first `n` Fibonacci numbers, than each `f(n)` whould typecheck against `FList[Int, n]`, in this case can write the type of `f` as
```
∀\n : Nat, FList[Int, n]
```
In words: “(`f` is) for each natural number `n`, a list of integers of length `n`”. Such types are called dependent function types. The notation `X -> Y` is a shorthand for `∀\x : X, Y` for the case `Y` does not depend on `x`.

The use of universal quantifier `∀` is justified by the fact that our type system is expressive enough to encode propositions (like “`n` is even” or “`n` is greater than `m`”) as types (`IsEven[\n : Nat]`, `IsGreater[\n \m : Nat]`) inhabited by proofs of these propositions, and a proof that a predicate `P[\x : X]` holds for each `x : X` is precisely a term of the type `∀\x : X, P[x]`. It is also true that for two propositions `A` and `B`, an constructive proof that `A` implies `B` is a term of the type `A -> B` (such term is the thing that yields a proof of `B` whenever we have a proof of `A`).

Parameters (written `x :⁰ T`) can be seen as arguments which are not allowed to be used in the body of function (they in particular, they cannot be inspected and cannot be returned by the function), but can be used in type annotations. Parameters are allowed to be of any type, not neccessarily a datatype, so they can be used to define generic functions:
```
id := (\X :⁰ ﹡) ↦ (\x : X) ↦ x
-- trivial function that simply returns what it gets as argument

map := (\T :⁰ ﹡, \f : T -> T, \list : List[T]) ↦ ...
-- applies `f` to each element of the `list`
```
Types of such functions are denoted as follows:
```
id : ∀\X :⁰ ﹡, X -> X

map : ∀\T :⁰ ﹡, ∀\f : T -> T, List[T] -> List[T]
```

Using a parameter of type `Nat` (which is an ordinary datatype), we can write down the type of functions on lists that preserve list length:
```
∀\n :⁰ Nat, FList[X, n] -> FList[Y, n]
```

Owing to Propositions-as-Types, parameters can be also used to put conditions on function arguments:
```
(\n \m : Nat, p :⁰ IsGreater[n, m]) ↦
```

Zero superscript means, the variable is allowed to be used in the body exactly zero times. The notation is inspired by Quantitative Type Theories: Besides arguments that can be used multiple times and parameters that are not allowed to be used in function body, most Quantitative Type Theories also support resources `(\x :¹ MutuallyExclusiveResource)`, variables that have to be used exactly once.

Annotated lambda terms can be stripped of their annotations and parameters to bare terms, this procedure is known as erasure. If two lambda terms `f` and `g` are identical as bare terms (i.e. with type annotations stripped), we'll write `f ⩦ g`. To give an example, `(\x : Nat) ↦ x ⩦ (\x : AnyOtherType) ↦ x ⩦ (\X :⁰ ﹡) ↦ (\x : X) ↦ x`, the term we already introduced as `id`. The type `∀\x :⁰ X, Y[x]` can be seen as an (in general infinitary) intersection type on the level of bare terms: it is the type of terms which simultaneously typecheck against all `Y[x]` for every `x : X` if annotated accordingly. In particular the type `∀\x :⁰ X, Y` with `Y` a datatype independent of `X`, is equivalent to `Y` itself. The type `∀\x : X, Y[x]` is quite a different beast: on the bare level it is never a term that typechecks as `Y[x]`, it has one lambda-abstraction more on the outside to accomodate additional argument `x`.

Now let's clarify which types are datatypes:
* `∀\x : X, Y` requires both `X` and `Y` to be datatypes and defines a datatype;
* `∀\x :⁰ X, Y` does not require `X` or `Y` to be datatypes and defines a datatype iff `Y` is;
* `﹡` is a type, but never a datatype.

Since it is not allowed to write `X -> Y` if `Y` is not a datatype, we'll use `X -> Y` for `∀\x :⁰ X, Y` in such cases. It causes no problems, since it makes no sense write `∀\x :⁰ X, Y` for datatypes `Y` independent of `x` (such type is simply equivalent to `Y`) as mentioned earlier. That being said, let's give a few examples: `Nat -> ﹡` (sequence of types), `﹡ -> ﹡` (type parametrized by type) or even `(Nat -> ﹡) -> ﹡ -> ﹡` (type parametrized by a type and a sequence of types) are all valid types, but none of them is a datatype.

§ Encoding Nat in Core Cedille
------------------------------

Church numerals are terms of the following form:
```
zero := (\T :⁰ ﹡, step : T -> T, base : T) ↦ base
once := (\T :⁰ ﹡, step : T -> T, base : T) ↦ step(base)
twice := (\T :⁰ ﹡, step : T -> T, base : T) ↦ step(step(base))
thrice := (\T :⁰ ﹡, step : T -> T, base : T) ↦ step(step(step(base)))
```

If a number `n` is given in form of a Church numeral, any function can be iterated `n` times simply by applying `n` to that function:
```
(twice f)(x) = f(f(x))
```

Church numerals could be called “function iterators”. We can easily write down the type of Church numerals
```
Natᶜ := ∀\T :⁰ ﹡, (T -> T) -> T -> T
```
and the successor function
```
succ(\n : Natᶜ) := (\T :⁰ ﹡, step : T -> T, base : T) ↦ (n[T] step)(step(base))
```

Church numerals can only iterate functions returning values of the same type as their arguments, i.e. functions `f` of the type `∀\T : ﹡, (T -> T)`. Can we possibly iterate a function of a more general type? Yes, theoretically type `T` could be indexed over some type `I`, and its index could change every time we apply the function `f`. Let's call the index updating function `g` and write down signatures of `f` and `f'`:
```
g : I -> I
T : I -> ﹡
f : ∀\i :⁰ I, T[i] -> T[g i]
```

It would be desirable if we could iterate such functions as well: for each Church numeral (“iterator”) `n` we want to have a “dependent iterator” `n'` acting on such `f`s in so that
```
(n' f) : ∀\i :⁰ I, T[i] -> T[(n g) i]
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

Under propositions-as-types interpretation of types `Natᴵ(n)` is precisely the statement we can perform mathematical induction (Nat-induction) up to `n`: given a predicate `T :⁰ Nat -> ﹡`, an induction step `step : T[n] -> T[succ n]` and the base case `base : T[zero]`, we obtain `T[n]` for arbitrary `n : Nat`:
```
Natᴵ[\n : Natᶜ] := ∀\T :⁰ (Natᶜ -> ﹡), ∀\step: ∀\m : Natᶜ, T[m] -> T[succ m]), ∀\base : T[zero]), T[n]
```

It turns out, we can actually easily provide typed lambda terms `zero' : Natᴵ[zero]`, `once' : Natᴵ[once]`, etc. Moreover they coincide with respective Church numerals as bare terms: `n ⩦ n'`.

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

Leibniz Equality is the principle that two things `\x \y : T` are called equal iff for any predicate `P : T -> ﹡` the proposition `P[x]` implies `P[y]`, if any statement about `x` is true, than so is the same statement about `y`. Leibniz equality principle defines equal as indiscernible. Under propositions-as-types interpretation, this principle can be reified as the following type (lhs and rhs stand for “left-hand side” and “right-hand” side respectively):  
```
Eq[\T : ﹡, \lhs \rhs : T] := ∀\P : (T -> ﹡), P[lhs] -> P[rhs]
```

We can easily provide a term stating every `x` is equal to itself:
```
refl(0 \T : ﹡, \x : T) := (0 P : T -> ﹡, e : P[x]) ↦ e
```
This property of equality is called reflexivity. Symmetry and transitivity for `Eq` can be also easily proved.

For structured objects (amongst other things, geometric structures such as graphs, and algebraic structures, such as groups, rings, etc.) it makes sense to talk about identifiablity instead of equality. An identification `p : Id[T][G, H]` between two objects `G` and `H` of type `T` (called isomorphism in case of algebraic structures) is a rule allowing to “transport” any construction `f(\x : G)` on `G` and any true statement `P[G]` about `G` into a construction on `H`/true statement `P[H]` about `H` and vice versa. By transporting true statements both ways, the notion of identifiability subsumes the notion of indiscernibility (“Leibniz equality”), but it extends it by acknowledging that there can be more than one way to identify things, and the choice of identification is substantial. (The recent insight, that identifications themselves are structured mathematical objects in their own right, and it makes a lot of sense to think about identifications between identifications, lead to a novel research area called Homotopy Type Theory.)

The type of identifications `p : Id[T][G, H]` can be defined in Intuitionistic Type Theories as an indexed inductive type, but it is not a W-type. Its defining features are the only constructor `refl(T, x) : Id[T][x, x]` and the “induction principle” known as the J-rule:
```
J(0 \T : ﹡, \x \y : T, p : Id[T][x, y]) :=
  ∀\P : (\a \b : T -> Id[T][a, b] -> ﹡),
  ((\t : T) -> P[t, t, refl(T, t)]) -> P[x, y, p]
```

Now let's try to apply the approach we already employed for W-types to construct the `Id`-type from `Eq` in Core Cedille:
```
Id[\T : ﹡, \x \y : T] := (
  \p : Eq[T][x, y],
  p : ∀\P : (\a \b : T -> Eq[T][a, b] -> ﹡),
    ((\t : T) -> P[t, t, refl(T, t)]) -> P[x, y, p]
)
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


§ Digression: Incompletely Instantiated Types
---------------------------------------------

As we have already seen, types can have parameters in Core Cedille, e.g. `List[T]` or `FList[T, n]`. In order to declutter code, one can introduce the following syntactic sugar, seemingly allowing incompletely instantiated types. We'll let to use the name of parametrised type without parameters on the right side of `:` in argument lists (in particular in lambda term definitions), which desugars by adding omitted parameters to the argument list left to the argument of incompletely instantiated type:
```
(l : FList) ↦ ...    ===    (0 l⍝T : ﹡, 0 l⍝length : Nat, l : FList[l⍝T, l⍝length]) ↦ ...
```

The names of the invisible parameters are generated by concatenating the name of the argument, special connecting symbol (we found nothing better than `⍝` yet) and the name of the omitted parameter. For partial instantiation, the following syntax is proposed:
```
(n : Nat, l : FList[length ↦ n]) ↦ ...    ===   (n : Nat, 0 l⍝T : ﹡, l : FList[l⍝T, n]) ↦ ...
```


--->
