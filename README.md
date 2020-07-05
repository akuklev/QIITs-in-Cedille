Implementation of Martin-Löf style Equality Type and Quotient Inductive-Inductive Types in Cedille
==================================================================================================

§ Preliminaries: Notation and Type System
-----------------------------------------

We'll work in a system where terms don't in general have a canonical type, but can be typechecked against a given type, possibly nonunique. We'll write bare (untyped) lambda terms like `\x ↦ expr(x)` and lambda terms with typed variables like `(\x : Nat) ↦ expr(x)`. A typed lambda term can be checked against it type: if for a term `f := (\x : X) ↦ expr(x)` the term `expr(x)` typechecks against type `Y`, the term `f` typechecks against `X -> Y`. Such types are called function types. In general, the type `Y` can be dependent on the variable `x`: consider a function `f(n : Nat)`, generating some list of integers of length `n`, say first `n` Fibonacci numbers, than each `f(n)` whould typecheck against `List[Nat, length = n]`, in this case can write the type of `f` as `(\n : Nat) -> List[Int, length = n]`. Such types are called dependent function types. Note the notational difference between lambda terms and dependent function types: `↦` vs `->`.



`f ⩦ g` t
