# Design of openverse

openverse is a reference implementation of Verse. "Reference" means the
meaning of every accepted program is fixed by a definition that can be read,
proved about, and run. That definition is the big-step semantics of Verse
Core in Lean. Everything else, the front end and the C runtime, is checked
against it. This page records the decisions behind the shape of the code.

## Two languages, one semantics

Surface Verse is large and changing (the Book of Verse tracks a development
branch). Verse Core (`OpenVerse/Core/Syntax.lean`) is small: literals, slot
reads and writes, sequencing, 29 primitives, calls, `if`, single-generator
`for`, `loop`, `break`, `return`, `Print`. Every surface construct is a
*derived form*:

- `not`, `or`, `and`, `option{}` and `logic{}` are built from `if`
  (`Core/Derived.lean`), and the rollback laws the Book states are theorems
  about these definitions;
- multi-generator `for` is nested single-generator `for` plus `flatten`;
- comparison chains use temporaries, so each operand is evaluated once;
- structs are tuples, enums are ints, and maps are arrays of pairs in
  insertion order.

Keeping Core small keeps the proofs and the C runtime small. All 29
primitives are one Lean function (`Prim.apply`) and one C file
(`runtime/src/prims.c`).

## Failure and rollback

Verse's failure is not an exception. A failable expression in a failure
context either succeeds, or fails and leaves no trace. The semantics makes
this literal. The state is the current frame together with the output, and
the rules for a failure context (`Eval.ite_fail`, `EvalFor.skip`) restart from
the state *before* the context.

Output is rolled back as well. A `Print` in a condition that fails is not
observed, which is the reading of "nothing changes" in Book §6.3.

Because Verse has no closures and frames are not shared, a callee cannot
write its caller's frame. So rollback only ever restores slots of the frames
that are live. The C runtime implements this with one value stack and an
undo journal (`runtime/src/store.c`):

- writes are logged only inside failure contexts;
- a mark is a pair of lengths, journal and output;
- rolling back undoes entries newest first and truncates the output.

The QuickProof law `store_rollback_model` proves this against a naive
copy-the-whole-state model, for every sequence of 32 operations on up to 3
nested contexts (the bounds a VST proof needs; the code has no depth limit
of its own).

## Fuel

The interpreter `eval` takes fuel and spends one unit per nested
evaluation, so Lean accepts it as structural recursion. The relational
semantics needs no fuel. Two theorems connect them:
- `eval_complete` is stated for *all* fuels above a bound, not just one.
- So `eval_fuel_irrelevant` follows: fuel decides whether the interpreter
  finishes, never what it returns.

Determinism of the relation (`Eval.det`) is then a corollary rather than a
separate induction.

Fuel also gives a well-founded measure for proofs where structural
recursion on derivations does not work. The prime example is type
preservation, where a call's body must first run its initialisation prefix
(`TypeSafety.lean`, strong induction on fuel).

The C runtime counts fuel exactly as Lean does. On every program of the
test suite, the smallest fuel that does not run out is the same in both
implementations.

## Translation validation instead of a verified front end

The parser and elaborator are ordinary code (`partial def`) and are not
proved correct. Each program they produce is checked by decidable functions
that are proved to establish the hypotheses of the core theorems:

| Check | Proved to give | Used by |
|---|---|---|
| `Prog.checkEffectSound` | `Prog.EffectSound` | `<decides>` soundness, `Eval.no_fail` |
| `Prog.checkWellScoped` | `Prog.WellScoped` | `Eval.scoped_ok` |
| `Prog.checkTypes S Γs` | `ProgTyped P S` | type safety, `Eval.typed` |
| `Prog.checkControl` | `break` stays in its loop | `Eval.no_control` |

The type check needs a certificate: the signature of every function and the
type of every slot. The elaborator knows both, since it allocates each slot
with a type.

An elaborator bug therefore cannot make a program that runs violate a
theorem: such a program is rejected with "internal error". The front-end
fuzzer (`scripts/fuzz-front.sh`) mutates real sources to look for such
rejections and for crashes. It found one, a stack overflow on recursive
structs, now rejected.

## Why every slot starts with a typed default

The semantics starts a call's non-parameter slots as `void`, which keeps the
Core and the binary format free of types. A type invariant of the form
"every slot holds a value of its type" is then false at function entry. The
alternative, a flow-sensitive definite-assignment analysis, would have to
model rollback.

Instead, the elaborator begins every body with an initialisation prefix that
stores the default of each slot's type (`initPrefix`), and the type checker
recognises the prefix (`stripPrefix`). This needs no change to the format
or to the C runtime. It costs a few stores per call.

## The binary format and the loader

The C runtime does not parse Verse; it loads OVBC (`docs/FORMAT.md`). Each
function is a post-order node table, so every child index is smaller than
its parent's. One forward pass can then check the whole program, and the
loader needs no recursion, which matters for a VST proof. Compound literals
are emitted as the primitives that build them, so every node is flat.

The loader's acceptance conditions are exactly `Prog.WellScoped`. By
`Eval.scoped_ok`, a program it accepts never raises a slot or call error.
So the interpreter needs no slot checks of its own (it keeps cheap ones
anyway).

## Two semantics, one seam

The C runtime is proved under CompCert's semantics of C, with QuickProof.
Lean cannot reason about C, and Coq does not know the Lean definitions.
Following LeanOS (ADR 0030), each seam is a formula that both sides state.

The arithmetic seam is the tightest. `Seams.lean` restates the C law's
formulas symbol for symbol and proves in Lean that each one is `Prim.apply`.
QuickProof proves in Coq that the C functions compute those formulas. The
remaining trusted step is reading that the two texts are the same formula
(`docs/SEAMS.md`).

The interpreter itself is not proved. It is a transcription of
`Interp.lean`, and it is compared with the Lean interpreter on the Verse test
suite, on thousands of random Core programs that exercise every node and
every outcome kind (`OpenVerse/Core/Gen.lean`), and on front-end mutants. It
also runs under ASan/UBSan.

## Readings of the Book

Where the Book of Verse is silent or contradicts itself, openverse takes
one reading and records it in `docs/LANGUAGE.md`. The most consequential:

- `int` is 64-bit with overflow as a runtime error, as on BPVM. The other
  choice, VerseVM's unbounded integers, would need bignums in the C runtime.
- comparisons return their left operand;
- a failing `for` body makes the `for` fail, as in the Verse Calculus.
