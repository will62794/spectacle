## 2023-01-08

May want to have a better way for syncing UI model state with URL query parameters e.g. on every update to the model, re-sync the necessary subset of state we want to store in the URL query path.

## 2024-01-26

May be able to use eval graph as structure for compiling to lower level representation (e.g. C++), but think I may need to also record evaluation order, which matters for how eval nodes process incoming values. For example, conjunctions may need to process children in proper order so that contexts are updated appropriately. For disjunctions, I don't think this holds true, since contexts coming back can be process (and combined) in any order.

## 2024-07-10

[Github search](https://github.com/search?q=%3D%3D+INSTANCE+language%3ATLA&type=code&ref=advsearch&p=2) of uses of `INSTANCE` across TLA+ code. Parameterized insantiation seems quite rare. [This search](https://github.com/search?q=%22%29+%3D%3D+INSTANCE%22+language%3ATLA&type=code&ref=advsearch) is somewhat more accurate.

Note that for `INSTANCE` module imports, it is the case that only `VARIABLE` and `CONSTANT` declarations can be valid targets for substitution. As reported in one the TLC error messages:

```
Identifier 'ExprM3' is not a legal target of a substitution. 
A legal target must be a declared CONSTANT or VARIABLE in the module being instantiated. 
(Also, check for warnings about multiple declarations of this same identifier.)
```
for a spec that looks like
```tla
---- MODULE simple_extends_instance ----
EXTENDS Sequences, Naturals

INSTANCE simple_extends_M3 WITH ExprM3 <- 43

VARIABLES x

Init == 
    \/ x = ExprM3 + 3

Next == x' = x

====
```
where `simple_extends_M3` contains a definition for `ExprM3`.

## 2024-07-12

TODO: Reconsider clone calls throughout in expression evaluation, in cases where copies may not be strictly necessary.

## 2024-12-24

Note that in general there may be more work needed to precisely handle evaluation of expressions with respect to definition context. For example, the JS interpreter seems to handle the following spec currently:

```tla
---- MODULE simple2 ----
EXTENDS Naturals

VARIABLE x

A == B + 2

B == 1

Init == 
    /\ x = [i \in {0,A} |-> {}]

Next == 
    \/ \E b \in {0,A}, c \in {88,99} : x' = [x EXCEPT ![b] = x[b] \cup {c}]

====
```
but is rejected by TLC, because the definition of `B` is not in scope yet when `A` is defined. This could work in theory but TLC/TLA+ seems to define definitions in a way such that their evaluation is tied to the definitions that were in scope at the time they were defined. May need to thread a few changes through the interpreter to make this work in all cases and match TLC. 

This may also help iron out the subtleties related to lazy evaluation, where we want to evaluate defined expressions in different contexts/scopes.

## 2024-12-30

Note that in TLC configuration files, there are *assignments* (`=`) and *replacements* (`<-`), which are subtly different.

For an **assignment** `c = v`, it is the case that `c` is a constant parameter *or* a defined symbol and `v` is a value. 

For a **replacement** `c <- d`, though, it is the case that `d` is a defined symbol.

## 2024-12-31

Still TODO: properly work out how to capture "current context" for current variables, declarations, definitions that appeared *at the time* a definition was defined, and how to properly make this available in the interpreter.

## 2025-01-04

Whenever we evaluate an identifier that refers to something else i.e. a definition, we can consider this as moving into a new "scope". That is, the definitions/declarations that we had access to in the original expression may no longer be "in scope" for the new definition that is being evaluated.

For substitutions, that can be defined by module instantation, for example, this means that in the scope of evaluating a definition, we may also need to consider these naming substitutions. For any definition, it has a scope of "current definitions" but also a set of "substitutions". Note that for a substitution like

```tla
h == 2
INSTANCE M WITH val <- h
```
the substitution expression `h` also has its *own* scope of "current definitions", which is defined by the point of the `INSTANCE` declaration.

Note that module substitutions can refer to either `CONSTANT` or `VARIABLE` declarations (note that *declarations* are different from *definitions*).

In general, if we expanded all definitions fully (i.e. apply all reductions), what is the role of "scopes" or "contexts" in this world? Is this helpful when thinking about a more unified model of definitions and "scoping"? 

If we expand all definitions fully, then, as Lamport notes, a top-level formula should only refer to

> variables, primed variables, model values, and built-in TLA+ operators and constants.

## 2025-01-05

Also need to consider the case of "global" definitions that may have name clashes?
e.g.
```tla
---- MODULE simple_extends_instance ----
EXTENDS Sequences, Naturals

H1 == INSTANCE simple_extends_M3
H2 == INSTANCE simple_extends_M4
VARIABLES x

Init == 
    \/ x = H1!ExprM3 + 3 + H2!ExprM3

Next == x' = x

====
```

where 

```tla
---- MODULE simple_extends_M3 ----
EXTENDS Sequences

ExprM3 == 43

====
```

```tla
---- MODULE simple_extends_M4 ----
EXTENDS Sequences

ExprM3 == 45

====
```


## 2025-01-13

Need to continue working on and finish off conversion to have definitions stored and referenced by globally unique identifier ids, and all evaluations of identifers occur based on the "current context" in which those definitions were defined. Need to also make sure substitutions for module instantiations are working correctly.

Also need to deal with function definitions, which I feel like could ultimately be merged into all other definition handling, and not made separate?

## 2025-03-26

Should it be the case that we really only need to clone at most as many times as there are branching choice calls in the expression? Have to think on that one.

## 2025-05-17

Don't think object class instances (e.g. `TLAState`) can be directly serialized and passed to/from a WebWorker. Ran into this when trying to improve trace loading computation that is delegated to web worker thread. Probably not that hard to work around, but just need to be clear on an approach to move these state objects between UI thread and web worker.

Basically we can tune our serialization method to just be compatible with what Javascript does to a class instance object when calling `structuredClone` on it. It will apparently keep fields and stuff, but prototype chains, class instance info will not be preserved.

## 2025-05-19

Subtle bug in UI when generating action names based on quant bound values. Need to investigate to ensure action UI params shown are correctly mapped to underlying next state choice.

## 2025-05-22

Also see https://shopify.engineering/understanding-programs-using-graphs
