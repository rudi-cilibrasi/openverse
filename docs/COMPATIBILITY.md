# Compatibility with Epic's Verse

This page says how closely openverse matches Epic's own Verse, and how we
know. The numbers below are measured, and `scripts/check.sh` fails when they
stop being true.

## The short answer

<!-- scoreboard-summary:begin -->
Epic's shipped compiler and Verse VM (UEFN 43.12) have answered 539 probe programs. openverse
gives the same answer on 478 of them and a different one on 61:

- **41** gaps: Verse that Epic admits and runs, and openverse refuses because the form is not implemented. openverse says so at compile time; it does not run these programs wrongly.
- **9** where Epic stops with an internal error or stalls, and openverse computes the result.
- **3** where openverse has a form of the Book of Verse that 43.12 does not ship yet.
- **3** library names Epic keeps internal or restricted, which openverse lets a program use.
- **4** kept on purpose, where Epic's behaviour is unspecified or not worth imitating.
- **1** caused by the probe's form, not the language.
<!-- scoreboard-summary:end -->

Every difference is listed under [Every difference](#every-difference), with
Epic's output, openverse's, and the cause.

## What the target is

openverse targets **Epic's Verse VM** wherever it and the older Blueprint VM
disagree (the owner's decision, 2026-11-18). The evidence is one build:
UEFN 43.12, `++Fortnite+Release-43.12-CL-60598086`, sessions launched with
"Use Verse VM", recorded between 2026-11-18 and 2026-11-20 on a Windows
machine ([#724](https://github.com/rudi-cilibrasi/openverse/issues/724)).
No Epic compiler or VM runs on the machines this repository is developed
on, so every Epic result here is a recorded one:
[`results/epic-43.12-compile.tsv`](../tests/conformance/versevm/results/epic-43.12-compile.tsv),
[`results/epic-43.12-runs.tsv`](../tests/conformance/versevm/results/epic-43.12-runs.tsv)
and the `epic_outcome` and `epic_lines` columns of each probe directory's
`expectations.tsv`.

Where the Book of Verse and the shipped compiler disagree, openverse follows
the shipped compiler when it refuses a program, and keeps the Book's form
when the Book has something 43.12 does not have yet (the `book-ahead` rows).

## How a probe is judged

A probe is a small program under
[`tests/conformance/versevm`](../tests/conformance/versevm) that prints
marked lines. Epic compiled each one alone, and ran the ones it admitted.
openverse runs each in its Lean interpreter and its C runtime, which must
agree with each other. The two results are **the same** when both refuse the
program, or both run it and print the same lines, or both stop with a
runtime error after the same lines. Where Epic's compiler admitted a probe
that was then not run, the probe counts as **admitted by both** if openverse
admits it too; what it prints is unchecked.

Two things are not compared. Diagnostics: a refusal matches a refusal,
whatever the wording, and openverse's messages cite Epic's error code where
the rule came from one. And `Print` inside a context that fails: the Verse VM
logs such a line labelled `(Rolling Back)`, and openverse drops it, so those
lines are left out of Epic's side ([the ten probes](../tests/conformance/versevm/followup-print)
show that the labelled lines are exactly the ones openverse drops).

## What this does not tell you

- **It is a sample, not a proof.** The probes were written to ask questions:
  where the Book and openverse disagreed, where Epic's two VMs were reported
  to differ, and 122 programs of ordinary runtime semantics. A program
  outside them can still differ.
- **One build.** Epic changes Verse between releases; the answers are
  43.12's.
- **Language only.** openverse has no Fortnite devices, no `session`, no
  player or persistence API. A probe is plain Verse with `Print`.
- **The Blueprint VM is not the target.** Where it differs from the Verse VM
  (integer overflow, `branch` lifetime, compound assignment, module
  constants) openverse does what the Verse VM does.
- **16 probes are not asked yet** (`followup-variance`, class variance of
  function values). They wait for the next Windows run.

The Book of Verse's own test suite is the second measure. Of its 13,504
cases, openverse agrees with 8,855, refuses 656 the Book calls valid, accepts
1 the Book says must be refused, prints something else on 36, and 3,956
cannot be translated by the harness
([the survey](research/book-test-conformance.md),
[baseline](../tests/conformance/book/baseline.tsv)). The Book is ahead of
43.12 in places, so a Book disagreement is not always an Epic one: the
probes above were how each was settled.

## Rules openverse took from Epic's results

Each links to where [LANGUAGE.md](LANGUAGE.md) states it.

- **Integers** are exact past 64 bits, up to 2^20 bits; `ToString` of one
  past 64 bits is a runtime error; a module's constants are evaluated in 64
  bits ([int](LANGUAGE.md#int)).
- **Compound assignment** resolves its place before the right operand runs
  ([mutation](LANGUAGE.md#mutation-macros-tooling)).
- **Effects.** A function without an effect specifier has `no_rollback`, so
  a failure context or `<transacts>` code cannot call it (3512). An event's
  `Signal`, `Await` and `spawn` have it too. The legacy readings are the
  flags `--default-rollback` and `--signal-rollback`.
- **Concurrency.** A `branch` belongs to the task that started it and
  outlives the function; a cancelled task stops its children before its own
  `defer` blocks run; `Sleep(0.0)` yields to the next update; `Signal`
  resumes awaiters, then calls subscribers.
- **Admission.** What 43.12 refuses, openverse refuses: function-value
  conversions that need a wrapper (3502; `--function-coercions` keeps them),
  calls that may not complete in a data member's definition (3582), joins
  with more than one nearest common supertype (3509, 3510), a `<concrete>`
  subclass's field without a default (3519), names that differ only in case
  (9200, 9002), identifiers that are too long (3655), enums of more than 256
  values (3552), and module constants that allocate a `var` (9003).

The full record, probe by probe and in the order it was learned, is
[research/versevm-live-conformance.md](research/versevm-live-conformance.md).

## Scoreboard

Regenerate this part with
`python3 tests/conformance/versevm/scoreboard.py --run --md docs/COMPATIBILITY.md`
after `lake build` and `make -C runtime`. When a difference is fixed, delete
its row from
[`known-differences.tsv`](../tests/conformance/versevm/known-differences.tsv);
the gate fails until the row is gone and this page is regenerated.

<!-- scoreboard:begin -->
| | Probes |
| --- | ---: |
| Probes Epic has answered | 539 |
| Same result (refused by both, or the same lines, or the same lines then a runtime error) | 423 |
| Admitted by both, not run on Epic | 55 |
| Different | 61 |
| Not asked of Epic | 16 |

The 61 differences by cause (each is listed below):

| Cause | Probes | Meaning |
| --- | ---: | --- |
| gap | 41 | Verse that UEFN 43.12 admits and runs, and OpenVerse refuses: not implemented yet |
| book-ahead | 3 | OpenVerse has a form of the Book of Verse that UEFN 43.12 does not have yet |
| restricted-name | 3 | A library name UEFN 43.12 keeps internal or restricted; OpenVerse lets a program use it |
| kept | 4 | OpenVerse's behaviour is kept on purpose, where Epic's is unspecified or not worth imitating |
| epic-defect | 9 | Epic stops or stalls where the language defines a result; OpenVerse computes it |
| harness | 1 | The probe's form, not the language: it uses a name only the UEFN device wrapper has |

### By probe set

A set is a directory of `tests/conformance/versevm` (`original`: the directory itself).

| Set | Probes | Same | Admitted by both | Different | Not asked |
| --- | ---: | ---: | ---: | ---: | ---: |
| `original` | 34 | 33 | 0 | 1 | 0 |
| `book` | 45 | 44 | 0 | 1 | 0 |
| `differential` | 122 | 122 | 0 | 0 | 0 |
| `fingerprint` | 4 | 4 | 0 | 0 | 0 |
| `followup` | 19 | 18 | 0 | 1 | 0 |
| `followup-3582` | 40 | 26 | 12 | 2 | 0 |
| `followup-book2` | 46 | 45 | 0 | 1 | 0 |
| `followup-book3` | 22 | 13 | 9 | 0 | 0 |
| `followup-book4` | 18 | 11 | 5 | 2 | 0 |
| `followup-coerce` | 37 | 14 | 23 | 0 | 0 |
| `followup-coerce2` | 17 | 11 | 6 | 0 | 0 |
| `followup-conc` | 24 | 23 | 0 | 1 | 0 |
| `followup-event` | 14 | 12 | 0 | 2 | 0 |
| `followup-int` | 27 | 19 | 0 | 8 | 0 |
| `followup-print` | 10 | 10 | 0 | 0 | 0 |
| `followup-refused` | 60 | 18 | 0 | 42 | 0 |
| `followup-variance` | 16 | 0 | 0 | 0 | 16 |

### Every difference

Lines are separated by `|`. Epic's column is the Verse VM's output, or its compiler's verdict.

#### `gap` (41)

Verse that UEFN 43.12 admits and runs, and OpenVerse refuses: not implemented yet.

| Probe | Epic's Verse VM | OpenVerse | Why |
| --- | --- | --- | --- |
| `castable-concrete-subtype` | ran: called | refused: tests/conformance/versevm/followup-refused/castable-concrete-subtype.verse:13:0: unknown parametric type 'castable_concrete_subtype' (only structs can be parametric) | UEFN 43.12 admits and runs it; OpenVerse refuses the library type castable_concrete_subtype |
| `castable-param-result-type` | ran: found 1 | refused: tests/conformance/versevm/followup-refused/castable-param-result-type.verse:14:14: unknown function 'Y' | UEFN 43.12 admits and runs it; OpenVerse refuses a castable_subtype parameter used as a type in its function's result |
| `castable-subtype-any` | ran: length 1 | refused: tests/conformance/versevm/followup-refused/castable-subtype-any.verse:13:0: castable_subtype(any): openverse writes castable_subtype of a class or an interface only, not of any (types as values: docs/research/t… | UEFN 43.12 admits and runs it; OpenVerse refuses castable_subtype(any) |
| `castable-subtype-of-param` | ran: bound | refused: tests/conformance/versevm/followup-refused/castable-subtype-of-param.verse:18:0: castable_subtype(t): openverse writes castable_subtype of a class or an interface only, not of t (types as values: docs/research/… | UEFN 43.12 admits and runs it; OpenVerse refuses castable_subtype(t) of a type parameter |
| `class-interface-same-field` | ran: class 12 interface 24 | refused: tests/conformance/versevm/followup-refused/class-interface-same-field.verse:21:27: X.(c_a:)Value: both has the field Value of c_a and the one of i_b: openverse keeps one field of a name in a class, so it cannot… | UEFN 43.12 admits and runs it; OpenVerse refuses a class's and an interface's fields of one name, told apart by qualifiers |
| `class-type-param-as-arg` | ran: empty | refused: tests/conformance/versevm/followup-refused/class-type-param-as-arg.verse:17:25: t, a type parameter, given as Nothing's type argument t: openverse takes the BPVM's reading, a link error (Book of Verse tests, Ty… | UEFN 43.12 admits and runs it; OpenVerse refuses a class's type parameter given as a type argument |
| `class-value-construct` | ran: value 7 | refused: tests/conformance/versevm/followup-refused/class-value-construct.verse:15:19: unknown struct 'ClassValue' | UEFN 43.12 admits and runs it; OpenVerse refuses a class bound to a local and constructed through it |
| `classifiable-subset` | ran: contains base_type | refused: tests/conformance/versevm/followup-refused/classifiable-subset.verse:18:4: unknown parametric type 'classifiable_subset' (only structs can be parametric) | UEFN 43.12 admits and runs it; OpenVerse refuses the library type classifiable_subset |
| `concatenate-maps-key-join` | ran: length 2 | refused: tests/conformance/versevm/followup-refused/concatenate-maps-key-join.verse:10:47: expected int, found string | UEFN 43.12 admits and runs it; OpenVerse refuses ConcatenateMaps joining maps whose keys are int and string |
| `concrete-subtype-bound` | ran: called | refused: tests/conformance/versevm/followup-refused/concrete-subtype-bound.verse:15:12: t:concrete_subtype(…) is not supported as a type parameter's bound: a concrete class's subclasses need not be concrete, so it is no… | UEFN 43.12 admits and runs it; OpenVerse refuses concrete_subtype(…) as a type parameter's bound |
| `constructor-delegation-archetype` | ran: label made extra 2 | refused: tests/conformance/versevm/followup-refused/constructor-delegation-archetype.verse:26:8: MakeBase<constructor>(…) delegates to a constructor: it can only be an item of a constructor's body; call it as MakeBase(…) | UEFN 43.12 admits and runs it; OpenVerse refuses MakeBase<constructor>(…) in an archetype outside a constructor |
| `fbounded-class` | ran: clone 13 | refused: tests/conformance/versevm/followup-refused/fbounded-class.verse:the Verse Core type of class item would contain itself, through its type arguments (#63) | UEFN 43.12 admits and runs it; OpenVerse refuses a class in its own parent's type argument (F-bounded) |
| `fn-type-named-signature` | ran: called | refused: tests/conformance/versevm/followup-refused/fn-type-named-signature.verse:11:16: a top-level definition must start at column 0 | UEFN 43.12 admits and runs it; OpenVerse refuses the function type `type{f():void}` with a named signature |
| `generic-arg-result-param` | ran: value 1 | refused: tests/conformance/versevm/followup-refused/generic-arg-result-param.verse:17:32: cannot infer type parameter u of Apply from the arguments of this call | UEFN 43.12 admits and runs it; OpenVerse refuses a type parameter given only by a generic argument's result |
| `generic-fn-local` | ran: value 1 | refused: tests/conformance/versevm/followup-refused/generic-fn-local.verse:14:9: 'Identity' is generic: a function type determining all its type arguments and satisfying its bounds must be expected (#214, #209) | UEFN 43.12 admits and runs it; OpenVerse refuses a generic function bound to a local |
| `infer-from-empty-array` | ran: count 0 | refused: tests/conformance/versevm/followup-refused/infer-from-empty-array.verse:16:32: cannot infer type parameter t of Count from the arguments of this call | UEFN 43.12 admits and runs it; OpenVerse refuses a type parameter given only by `array{}` |
| `join-fn-refinement-result` | ran: value 1 | refused: tests/conformance/versevm/followup-refused/join-fn-refinement-result.verse:16:66: the branches have different types: type{_():small} and type{_():int} | UEFN 43.12 admits and runs it; OpenVerse refuses function values joined at a refinement's base type |
| `join-fn-type-params` | ran: compiled | refused: tests/conformance/versevm/followup-refused/join-fn-type-params.verse:14:4: the branches have different types: type{_(:t):void} and type{_(:u):void} | UEFN 43.12 admits and runs it; OpenVerse refuses function values of two type parameters joined |
| `map-any-value-generic` | ran: count 2 | refused: tests/conformance/versevm/followup-refused/map-any-value-generic.verse:13:35: expected [t]any, found [int]string (in a call of MapCount) | UEFN 43.12 admits and runs it; OpenVerse refuses [int]string passed as [t]any |
| `map-literal-sibling-keys` | ran: looked up | refused: tests/conformance/versevm/followup-refused/map-literal-sibling-keys.verse:18:21: expected child_a, found child_b | UEFN 43.12 admits and runs it; OpenVerse refuses a map literal whose keys are of sibling classes |
| `module-const-empty-map-unique-key` | ran: length 0 | refused: tests/conformance/versevm/followup-refused/module-const-empty-map-unique-key.verse:13:0: the constant Empty would hold an object with var fields or of a <unique> class, which would be a new one at each use: mak… | UEFN 43.12 admits and runs it; OpenVerse refuses a module constant holding an empty map keyed by a <unique> class |
| `module-const-unique` | ran: same and different | refused: tests/conformance/versevm/followup-refused/module-const-unique.verse:18:0: the constant Instance1 would hold an object with var fields or of a <unique> class, which would be a new one at each use: make it a fun… | UEFN 43.12 admits and runs it; OpenVerse refuses module constants of a class<unique><allocates> |
| `named-fn-any-result` | ran: succ of 0 | refused: tests/conformance/versevm/followup-refused/named-fn-any-result.verse:20:9: expected type{_(:int):any}, found type{_(:int):int} | UEFN 43.12 admits and runs it; OpenVerse refuses a function named where a function with an `any` result is expected |
| `named-tuple-param` | ran: defaults 3 \| given 6 | refused: tests/conformance/versevm/followup-refused/named-tuple-param.verse:11:16: a named parameter inside a tuple parameter (?X) is not supported yet | UEFN 43.12 admits and runs it; OpenVerse refuses named parameters inside a tuple parameter |
| `named-tuple-value` | ran: value 5 | refused: tests/conformance/versevm/followup-refused/named-tuple-value.verse:15:32: a tuple with a named element (?Name := …) is not supported: the pinned Book of Verse does not settle such values, and named parameters i… | UEFN 43.12 admits and runs it; OpenVerse refuses a tuple value with a named element |
| `overloads-struct-and-array` | ran: one 1 many 2 | refused: tests/conformance/versevm/followup-refused/overloads-struct-and-array.verse:13:0: F is defined twice with parameters a call cannot tell apart, (a) and ([]a): overloads must take disjoint types | UEFN 43.12 admits and runs it; OpenVerse refuses the overloads F(:a) and F(:[]a) |
| `override-array-param` | ran: through base 2 | refused: tests/conformance/versevm/followup-refused/override-array-param.verse:16:4: derived.Method must have the signature of base.Method, which it overrides | UEFN 43.12 admits and runs it; OpenVerse refuses an override taking one []int where the overridden method takes two ints |
| `override-parametric-result-control` | ran: method gives 3 | refused: tests/conformance/versevm/followup-refused/override-parametric-result-control.verse:20:17: boxing a value of type $ext0 as a comparable here is not supported yet | UEFN 43.12 admits and runs it; OpenVerse refuses the control of override-parametric-result: boxing a value of an extension type as comparable |
| `override-parametric-result` | ran: method gives 3 | refused: tests/conformance/versevm/followup-refused/override-parametric-result.verse:18:4: sub_class.Method must have the signature of super_class.Method, which it overrides | UEFN 43.12 admits and runs it; OpenVerse refuses an override whose result is t where the overridden method's is comparable |
| `override-tuple-result` | ran: length 2 | refused: tests/conformance/versevm/followup-refused/override-tuple-result.verse:17:4: pair_getter.Get must have the signature of getter.Get, which it overrides | UEFN 43.12 admits and runs it; OpenVerse refuses an override with a tuple result over an array result |
| `override-wider-param` | ran: value 2 | refused: tests/conformance/versevm/followup-refused/override-wider-param.verse:17:4: derived.F must have the signature of base.F, which it overrides | UEFN 43.12 admits and runs it; OpenVerse refuses an override whose parameter is a superclass of the overridden one |
| `persistable-class` | ran: score 3 | refused: tests/conformance/versevm/followup-refused/persistable-class.verse:9:0: <persistable> classes are not supported yet (#11) | UEFN 43.12 admits and runs it; OpenVerse refuses a <persistable> class |
| `qualified-second-method` | ran: base 1 own 2 | refused: tests/conformance/versevm/followup-refused/qualified-second-method.verse:20:4: (derived:)F: a second method F beside the one derived inherits (Book of Verse ch. 10, "Methods with Same Name"): openverse does not… | UEFN 43.12 admits and runs it; OpenVerse refuses a second method `(derived:)F` beside an inherited F |
| `refinement-literal-local` | ran: negated -200 | refused: tests/conformance/versevm/followup-refused/refinement-literal-local.verse:16:4: an int is a negative_uchar only after a cast: write negative_uchar[X], which fails when X is not one | UEFN 43.12 admits and runs it; OpenVerse refuses a literal-bound local's negation at a refinement type without a cast |
| `refinement-overloads` | ran: negative 0 small 1 | refused: tests/conformance/versevm/followup-refused/refinement-overloads.verse:17:0: F is defined twice with parameters a call cannot tell apart, (small) and (negative): overloads must take disjoint types | UEFN 43.12 admits and runs it; OpenVerse refuses overloads on disjoint refinement types |
| `subtype-alias` | ran: called | refused: tests/conformance/versevm/followup-refused/subtype-alias.verse:13:0: unknown type 'class_of_c0' (supported: int, logic, char, string, void, []t, ?t, tuple(…), and structs and enums) | UEFN 43.12 admits and runs it; OpenVerse refuses a type alias of subtype(c) |
| `two-interfaces-same-method` | ran: a 12 b 21 | refused: tests/conformance/versevm/followup-refused/two-interfaces-same-method.verse:16:0: both inherits Method from both i_a and i_b: override it in both | UEFN 43.12 admits and runs it; OpenVerse refuses two interfaces' default methods of one name in one class |
| `type-argument-array` | ran: outer 2 | refused: tests/conformance/versevm/followup-refused/type-argument-array.verse:17:14: unexpected '[' | UEFN 43.12 admits and runs it; OpenVerse refuses `[]int` as a type argument |
| `unique-interface-equality` | ran: compiled | refused: tests/conformance/versevm/followup-refused/unique-interface-equality.verse:17:35: an operand of '=' must be comparable, and shape is a class (only <unique> classes are comparable, by identity) | UEFN 43.12 admits and runs it; OpenVerse refuses equality on an interface<unique> no class implements |
| `variance-contravariant-concat` | ran: method 1 | refused: tests/conformance/versevm/followup-refused/variance-contravariant-concat.verse:25:4: cannot concatenate []contravariant_class(int) and []contravariant_class_impl(comparable): contravariant_class_impl(comparable… | UEFN 43.12 admits and runs it; OpenVerse refuses arrays of a contravariant parametric class concatenated at two type arguments |
| `variance-covariant-join` | ran: joined | refused: tests/conformance/versevm/followup-refused/variance-covariant-join.verse:23:4: the branches have different types: covariant_class(int) and covariant_class(any): covariant_class is covariant in t: t is used in D… | UEFN 43.12 admits and runs it; OpenVerse refuses a covariant parametric class joined at int and any |

#### `book-ahead` (3)

OpenVerse has a form of the Book of Verse that UEFN 43.12 does not have yet.

| Probe | Epic's Verse VM | OpenVerse | Why |
| --- | --- | --- | --- |
| `book-int-shift-63` | refused: error 3506,3506 | ran: shift 63 above signed 64-bit max \| shift 200 round trip | BitShiftLeft and BitShiftRight are in the Book and its tests; UEFN 43.12 does not know the names (3506) |
| `subscribable-event-control` | refused: error 3506 | ran: after success 2 | subscribable_event is the Book's name; on UEFN 43.12 Subscribe is on event and the name is unknown (3506) |
| `div-const-for-choice-call-control` | refused | ran: count 2 | The choice operator `|` is in the Book; UEFN 43.12 has not implemented it (3101) |

#### `restricted-name` (3)

A library name UEFN 43.12 keeps internal or restricted; OpenVerse lets a program use it.

| Probe | Epic's Verse VM | OpenVerse | Why |
| --- | --- | --- | --- |
| `cancel-task-child` | refused | ran: branch cleanup \| runner cleanup \| cancelled \| after wait | task.Cancel is <epic_internal> on UEFN 43.12 (3593) |
| `sticky-event-subscribe` | refused | ran: subscribed \| sticky 2 \| after | sticky_event needs /Verse.org/Restricted on UEFN 43.12 (3506) |
| `todiagnostic-float-control` | refused | ran: diagnostic 15 | diagnostic's String is <epic_internal> on UEFN 43.12 (3593) |

#### `kept` (4)

OpenVerse's behaviour is kept on purpose, where Epic's is unspecified or not worth imitating.

| Probe | Epic's Verse VM | OpenVerse | Why |
| --- | --- | --- | --- |
| `long-ident-mangled` | refused | ran: field 42 | Epic's identifier limit (3655) is on a derived name that a parameter lengthens; OpenVerse applies the measured limits without parameters |
| `long-ident-function-param` | refused | ran: result 42 | Epic's identifier limit (3655) is on a derived name that a parameter lengthens; OpenVerse applies the measured limits without parameters |
| `long-ident-method-param` | refused | ran: method 7 | Epic's identifier limit (3655) is on a derived name that a parameter lengthens; OpenVerse applies the measured limits without parameters |
| `subscribe-order` | ran: c 1 \| b 1 \| a 1 \| c 2 \| b 2 \| a 2 \| a 3 \| b 3 \| c 3 \| after | ran: a 1 \| b 1 \| c 1 \| a 2 \| b 2 \| c 2 \| a 3 \| b 3 \| c 3 \| after | Subscribers are called in subscription order; the Verse VM's order varies from one Signal to the next (the API: "randomised"), so no program may rely on it |

#### `epic-defect` (9)

Epic stops or stalls where the language defines a result; OpenVerse computes it.

| Probe | Epic's Verse VM | OpenVerse | Why |
| --- | --- | --- | --- |
| `div-const-class-block` | refused | ran: size 3 | Epic's linker reports a cycle (9000) for a module constant built from a class whose block calls a function of the module; no rule of the language refuses it |
| `int-div-zero-big` | runtime-error: (no lines) | ran: quotient failed \| mod failed \| floor failed | Epic's native stops with ErrRuntime_GeneratedNativeInternal, "Value exceeds the range of a 64 bit integer", for an int past 64 bits; OpenVerse computes the exact result (the owner's decision, #724): Quotient |
| `int-euclid-big` | runtime-error: (no lines) | ran: quotient -4 \| mod D - 1 \| floor -4 \| ceil -3 | Epic's native stops with ErrRuntime_GeneratedNativeInternal, "Value exceeds the range of a 64 bit integer", for an int past 64 bits; OpenVerse computes the exact result (the owner's decision, #724): Quotient |
| `int-intrinsics-big` | runtime-error: min max | ran: min max \| clamp \| sgn \| containers equal | Epic's native stops with ErrRuntime_GeneratedNativeInternal, "Value exceeds the range of a 64 bit integer", for an int past 64 bits; OpenVerse computes the exact result (the owner's decision, #724): Clamp |
| `int-length-max` | stalled: (no lines) | ran: longest computed \| longer than half | Epic's multiplication whose result reaches 2^20 bits never returns and the session has to be replaced; OpenVerse computes up to 2^20 bits (the Book's MaxLengthBits) and raises the overflow error past it |
| `int-length-over` | stalled: (no lines) | runtime-error: half computed | Epic's multiplication whose result reaches 2^20 bits never returns and the session has to be replaced; OpenVerse computes up to 2^20 bits (the Book's MaxLengthBits) and raises the overflow error past it |
| `int-length-steps` | stalled: step 1 \| … \| step 19 | runtime-error: step 1 \| step 2 \| step 3 \| step 4 \| step 5 \| step 6 \| step 7 \| step 8 \| step 9 \| step 10 \| step 11 \| step 12 \| step 13 \| step 14 \| step 15 \| step 16 \| step 17 \| step 18 \| step 19 | Epic's multiplication whose result reaches 2^20 bits never returns and the session has to be replaced; OpenVerse computes up to 2^20 bits (the Book's MaxLengthBits) and raises the overflow error past it |
| `int-mod-big` | runtime-error: before mod | ran: before mod \| mod D - 1 | Epic's native stops with ErrRuntime_GeneratedNativeInternal, "Value exceeds the range of a 64 bit integer", for an int past 64 bits; OpenVerse computes the exact result (the owner's decision, #724): Mod |
| `int-mod-zero-big` | runtime-error: before mod | ran: before mod \| mod failed | Epic's native stops with ErrRuntime_GeneratedNativeInternal, "Value exceeds the range of a 64 bit integer", for an int past 64 bits; OpenVerse computes the exact result (the owner's decision, #724): Mod |

#### `harness` (1)

The probe's form, not the language: it uses a name only the UEFN device wrapper has.

| Probe | Epic's Verse VM | OpenVerse | Why |
| --- | --- | --- | --- |
| `compound-module-entry` | ran: entry 8 9 | refused: tests/conformance/versevm/compound-module-entry.verse:6:0: the module-scoped var Entries is keyed by session, which is not a class with <module_scoped_var_weak_map_key> (Book of Verse ch. 3: "The key type must … | The probe keys a module-scoped weak_map by session, which only the UEFN device wrapper has; OpenVerse runs its own module-scoped entries the same way (entry 8 9) |
<!-- scoreboard:end -->
