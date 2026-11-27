# Choice compared with the Verse team's prototype

Epic's UEFN 43.12 has no choice operator (it refuses `|` with error 3101), so openverse's choice
cannot be checked against Epic's VM. It can be checked against the Verse team's own prototype,
[`augustss/verse-semantics`](https://github.com/augustss/verse-semantics): a Haskell
implementation of the rewrite rules of "The Verse Language: its type system and semantics"
(the OPLSS 2026 "Supporting Figures" paper), by the paper's authors. This page records that
comparison, made on 2026-11-26 against the prototype at `d0eababf` and openverse at `b24ac5c5`.

## Result

- On 5,000 random programs in the fragment both accept, openverse and the prototype give the
  same values in the same order, with the same repetitions, on every one the prototype finishes
  (all but 24).
- openverse refused one form the prototype has: a choice in the body of a `for`. It is supported
  now (`docs/LANGUAGE.md`, [Choice](../LANGUAGE.md#choice), "In the body of a `for`"), with the
  prototype's results.
- No disagreement on a value was found.
- The two differ in how they parse a range beside a choice, and the prototype takes a range as a
  choice anywhere, which the Book does not allow (below).

## What the two can be compared on

The prototype has no effects, and openverse has no logic variables, so the common ground is
pure choice:

| Prototype | openverse |
| --- | --- |
| `all{c1; c2; e}` | `for (c1, c2, R := e) { R }` |
| `x := e` | `X := e` |
| `(a\|b)`, `a+b`, `a*b`, `a-b` | the same |
| `a<b`, `a<=b`, `a>b`, `a>=b`, `a<>b`, `a=b` (the left operand, or failure) | the same |
| `if(a<b){c}else{d}`, `if(q:=a; q<b){c}else{d}` | `if (A < B) then C else D`, `if (Q := A, Q < B) then C else D` |
| `one{e}` | `first{e}` |
| `not(a<b)` as a clause | `not (A < B)` |
| `(a,b)[i]` | `(A, B)(I)` |
| `a := for(x:=e){b}`, `a[i]`, `Length[a]` | `A := for (X := e) { b }`, `A[I]`, `A.Length` |
| `all{…; for(k:=e){b}}` (the values are arrays) | `for (…, R := for (K := e) { b }) { R }` |
| `f(a:int)<closed>:int := e`, `f[x]` | `F(A:int)<computes><decides>:int = e`, `F[X]` |
| `f(a:int,b:int)<closed>:int := e`, `f[x,y]` | `F(A:int, B:int)<computes><decides>:int = e`, `F[X, Y]` |
| `a := array{e1,e2}`, `a+b`, `x:a` as a clause | `A := array{e1, e2}`, `A + B`, `X : A` |

Two of the Book's rules shape the openverse side and do not change the values: a `for` needs a
generator or a clause that can fail, so every header starts with `D : array{0}`; and a filter
must be able to fail, so the generated filters are comparisons.

The prototype's tester compares the `all` of both sides of a `testeq`, so it observes order and
repetition. Each random program is run on openverse, and its result becomes the expected value
of a `testeq` case for the prototype (`--assume-verified`, which skips the prototype's verifier
for function definitions).

## Numbers

| Batch | Programs | Agree | Refused by openverse | Differ |
| --- | ---: | ---: | ---: | ---: |
| Expressions and bindings, depth 2 to 4, main at `652a0f1d` | 1,350 | 1,350 | 0 | 0 |
| With functions, arrays, `not`, binding conditions, main at `652a0f1d` | 1,500 | 1,430 | 70 | 0 |
| The same generator, with a `for` body's choice supported, at this change | 2,000 | 2,000 | 0 | 0 |
| With programs whose values are the arrays of a `for`, its body's choices included | 1,000 | 1,000 | 0 | 0 |
| With array literals and joins, generators over arrays, recursive and two-parameter functions, inner `for`s with two clauses and a filter | 2,050 | 2,026 | 0 | 0 |

In the last batch the other 24 programs ran past the prototype's step or time limit, so they
have no verdict. All 70 refusals in the second batch were a choice, or a call of a function with several values,
in the body of a `for`.

## The `for` body

In the prototype a `for` whose body has a choice has several values, one array for each
combination, the first iteration's choice varying slowest (its test `For7`):

```
for(x:=1|2|3){4|x}
(4,4,4) (4,4,3) (4,2,4) (4,2,3) (1,4,4) (1,4,3) (1,2,4) (1,2,3)
```

This follows from the paper's rules: MFOR (Fig. 14) and FOR (Fig. 13) make each iteration's body
an element of the array that `cons2` builds, so the bodies' choices are choices of the array,
and CHOICE splits the leftmost first.

openverse now does the same by a source rewrite before choice inlining
(`Choice.forProducts`):

```
for (cs) { b }   ⟶   $forProduct[for (cs) { for ($v := b) { $v } }, 0]
```

The inner `for` collects the values of the body for one iteration, which the clauses of a `for`
already do. `$forProduct` is a function with several values, written in Verse
(`forProductPrelude` in `OpenVerse/Front/Elab/Lowering.lean`) and taken lazily as any recursive
one is. Nothing in Core, the bytecode or the C runtime changed.

Nine programs of `tests/verse/for_body_choice.verse` were also run on the prototype, with the
same results: `For7`, a choice in the header and the body, first success, a branch with a
choice, a body with no value, no iteration, a `for` in a `for`, a `for` inside an expression,
and a `for` over the arrays of another (256 arrays).

What the prototype cannot say is when a body's effects happen, as it has none. openverse runs
every alternative of every iteration's body once, when the `for` is reached, as the clauses of
a `for` over the body's values do.

## Two differences: where `..` binds, and where a range may stand

The two parse a range beside a choice differently.

| Source | Prototype | openverse |
| --- | --- | --- |
| `7 \| 1..2` | `7 \| (1..2)`: 7, 1, 2 | `(7 \| 1)..2`: 1, 2 |
| `1..2 \| 7` | `(1..2) \| 7`: 1, 2, 7 | `1..(2 \| 7)`: 1, 2, then 1 to 7 |
| `1..2 = 2` | `(1..2) = 2`: 2 | `1..(2 = 2)`: 1, 2 |
| `1 \| 2 = 2`, `1 \| 2 > 1`, `1 \| 2 + 10` | `(1 \| 2) = 2`, `(1 \| 2) > 1`, `1 \| (2 + 10)` | the same |

In the prototype `..` binds tighter than `|` and than the comparisons, and looser than `+`. The
Book of Verse puts `..` at precedence 3, below the comparisons, `and` and `or` (ch. 4,
"Precedence"), and has no `|`. openverse follows the Book for `..`, and the prototype for `|`
against the comparisons and arithmetic. Those two together leave `|` tighter than `..`, which is
the one place the prototype is not followed: no order agrees with the Book on `..` and with the
prototype on both `|` and `..`.

A second difference is the Book's rule, not a matter of parsing. In the prototype a range is a
choice wherever it stands: `7 | (1..2)` is 7, 1, 2, and `one{1..3}` is 1. The Book says "Ranges
are not first-class values. They cannot be stored in variables or used outside of `for` loop
iteration clauses" (ch. 1), so openverse takes a range only as the source of a `for` clause, or
of a `first` with a generator, and refuses it as an alternative of a choice.

## Reproducing

The prototype needs GHC and cabal (`cabal build exe:tester`). A case is one line:

```
testeq("for7",pass) { for(x:=1|2|3){4|x} } { array{4,4,4} | array{4,4,3} | array{4,2,4} | array{4,2,3} | array{1,4,4} | array{1,4,3} | array{1,2,4} | array{1,2,3} }
```

run with `tester FILE.versetest --assume-verified -m 200000`. The generator is
`scripts/prototype-choice-diff.py OPENVERSE TESTER SEED COUNT [DEPTH]`; it prints every program
on which the two do not agree, and a tally.
