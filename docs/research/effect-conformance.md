# Effect contracts and admission

Issue [#494](https://github.com/rudi-cilibrasi/openverse/issues/494). The initial
inventory used main `34a4faa` (#506); implementation is integrated with #507.
OpenVerse checks heap permissions, failure and suspension. An annotation whose
contract it cannot enforce is now refused before function-value or continuation
lowering can erase it. This is the explicit-diagnostic option in #494, not an
implementation of prediction, convergence checking or foreign bindings.

## Source boundary

The specification snapshot is the [Book effects chapter at
`beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/13_effects.md).
It labels prediction **unreleased** and divergence checking **planned**, and
allows convergence declarations only for native functions, abstract methods
and function types. The [same snapshot's effect tests](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/Effects.versetest)
include duplicate/exclusive-effect refusals and reject obsolete `varies`.

Published Epic documentation is a separate reference. Its [native page](https://dev.epicgames.com/documentation/en-us/fortnite/native)
describes C++ implementation/code generation. Its [AddComponents API page](https://dev.epicgames.com/documentation/en-us/fortnite/verse-api/versedotorg/scenegraph/entity/addcomponents)
renders `predicts`, `dictates` and `no_rollback` together, with no explanation
in the first two effect rows, and says `no_rollback` cannot be manually
specified. Rendered SDK effect bits do not establish a user-annotation grammar
or prove a specific released engine enforces the Book's planned rules.
**No Epic compiler or multiplayer engine was run for this audit.** The
OpenVerse refusals below are explicit subset decisions; they do not claim
that every released UEFN compiler rejects the same annotations.

## Inventory

The table covers the effect vocabulary recognized by the admission policy,
including implicit/internal names found in the sources. Declaration metadata
is listed separately; accepting an access attribute does not imply a new
effect guarantee.

| Annotation or family | OpenVerse behavior | Classification and evidence |
| --- | --- | --- |
| No function heap annotation | Allows `allocates`, `reads`, `writes`. Callers pay declared permissions; constant effects and source-generated bridge effects are inferred under their existing rules. | Enforced OpenVerse default; not a server-authority or no-rollback promise. |
| `computes` | No heap permissions; excludes explicit heap permissions and `transacts`. Does not imply termination. | Enforced on functions and function types. [Heap cases](../../tests/verse/effects.verse), [recursion control](../../tests/verse/effect_admission_recursion.verse). |
| `reads`, `writes`, `allocates` | Allows the named heap permissions. Reading/writing mutable fields and mutable/unique allocation are checked, including indirect calls. Immutable values/local variables follow the existing heap model. | Enforced; [callbacks/defaults/generic/refining contexts](../../tests/verse/effect_admission_contexts.verse), existing `fx_*` diagnostics. |
| `transacts` | Allows all three heap permissions; excludes `computes` and `converges`. Rollback comes from the existing Core transactional semantics. | Enforced heap umbrella; no new native rollback guarantee. |
| `decides` | Failure contexts and bracket call syntax are checked; failure cannot be hidden through a function value. Cannot combine with `suspends`. | Enforced, with existing Core nonfailure checks. Runtime errors/fuel exhaustion are distinct from failure. |
| `suspends` | Suspension contexts, call restrictions, overrides, callback types and cancellation cleanup remain checked. A suspending constructor remains unsupported. | Enforced; [cleanup control](../../tests/verse/effect_admission_cleanup.verse), existing suspension contracts. |
| `predicts` | Refused in definitions, abstract signatures, callbacks/types, defaults and all loaded source, including unused declarations. | Explicitly rejected. No prediction call propagation or client/server execution model is advertised. [Direct](../../tests/errors/effect_admission_predicts.verse), [type](../../tests/errors/effect_admission_predicts_type.verse), [generated context](../../tests/errors/effect_admission_generated_context.verse). |
| `converges` | Refused even in the Book's eligible abstract/type/native contexts. Regular implementations are ineligible in the Book as well. A native tag cannot confer a trusted implementation. | Explicitly rejected. [Ordinary](../../tests/errors/effect_admission_converges.verse), [recursive](../../tests/errors/effect_admission_converges_recursive.verse), [abstract](../../tests/errors/effect_admission_converges_abstract.verse). Fuel is not a termination proof. |
| `no_rollback` | An explicit user annotation is refused. Existing output/events keep their transactional behavior. | Explicitly rejected annotation; intentional current transaction policy is tracked in [#495](https://github.com/rudi-cilibrasi/openverse/issues/495). |
| `dictates`, `diverges` | Explicit annotations are refused. OpenVerse models neither authoritative/predicting locations nor termination effect bits. | Explicitly rejected; loops and recursion remain available without a termination promise. |
| `succeeds`, `fails` | Explicit annotations are refused. Existing implicit success/failure discipline is unchanged. | Explicitly rejected spelling; cardinality enforcement is not removed. |
| `varies` | Refused as obsolete/unsupported, matching the pinned effect tests' rejection. | Explicitly rejected. |
| Duplicate effects | Refused in declarations and nested function types, including one occurrence before and one after a parameter list. | Enforced admission rule. [Declaration](../../tests/errors/effect_admission_duplicate.verse), [type](../../tests/errors/effect_admission_duplicate_type.verse). |
| Contradictory effects | Exclusive combinations, `computes` plus heap permissions, and `suspends` plus `decides` are refused before shape normalization. | Enforced for definitions and function types; existing declaration diagnostics retained. |
| Unknown function/type effects | Refused rather than discarded by function-shape normalization. | Explicitly rejected; [unknown specifier](../../tests/errors/effect_admission_unknown.verse). |

| Role or metadata | Behavior and boundary |
| --- | --- |
| `native`, `native_callable` | Refused as source annotations on retained declarations/types and at discarded field/struct sites. The source cannot create an FFI binding or bypass effect/type checks by adding a tag. Parser-supported enum syntax already rejects them. |
| Class/interface/struct heap budgets | Heap annotations are admitted and enforced. No heap annotation means all three permissions, also with metadata such as `unique` or `public`. `decides` and `suspends` are invalid on data types. [#508](https://github.com/rudi-cilibrasi/openverse/issues/508) enforces default/block/allocation budgets, inherited requirements and declared use-site charges. [Class](../../tests/errors/effect_admission_class_budget.verse), [interface](../../tests/errors/effect_admission_interface_budget.verse), [struct](../../tests/errors/effect_admission_struct_budget.verse). |
| Effects on fields, constants or modules | Refused where the annotation cannot describe the declared value. Field access metadata is separate. Constants retain effects inferred from their initializers; a forgotten `suspends`/`predicts` prefix cannot disappear. |
| Function declaration metadata | `public`, `internal`, `private`, `protected`, `override`, `final`, `abstract`, `constructor` retain their existing role-dependent handling. They are not function-type effects. This policy does not complete access/final-member semantics. |
| Other type/access metadata | Existing class/struct/enum/access rules and limitations remain separate from effect admission. This inventory does not certify every accepted non-effect attribute. |
| Compiler-only `$...` markers | Retained for generated protocols; the source lexer cannot spell these identifiers. The checked Core result remains the execution boundary. |

## Lowering, calls and proof boundaries

`EffectPolicy.check` runs at `elabProgramCore` before source rewriting, over
every loaded definition, parameter/field default, construction type argument,
nested function type, struct/refinement leaf and optional entry expression.
Struct annotations are retained through module and choice rewriting. Parser checks cover annotations discarded from fields, modules and
parametric type declarations. These checks apply to the ordinary and
`--no-choice` profiles, and all source CLI commands share them.

Materialized helper source and explicit function/method requests are checked
again before `FnValues.desugar` normalizes effect shapes. Public compiler APIs
cannot bypass the policy by supplying retained AST annotations or raw
function/method requests. Function types preserve the implemented effect sets;
invalid or unsupported bits do not become a weaker callback contract.

Supported calls keep the previous rules: an override cannot require extra
heap/failure/suspension effects; a callback must fit the expected effects;
generic calls and selected implementations pay their declared effects; omitted
defaults pay their actual effects at the caller, in their original scope and
order. Receiver capture, live state, rollback and cancellation cleanup are
unchanged. There is no additional prediction/convergence subtyping rule because
those declarations cannot be admitted.

Compiler-controlled intrinsics have fixed source/Core types and declared heap
permissions; source annotations cannot replace those bindings with unchecked
C++ implementations. User definitions of supported soft builtins still follow
ordinary source checking. This work adds no native binding mechanism.

No Core, runtime or proof input changes. Existing typed/nonfailure/control and
heap guarantees, including `Prog.accepted_no_writes`, retain their scope; see
[CLAIMS.md](../CLAIMS.md). The new pass is an executable frontend admission
check, not a Lean proof of frontend correctness or termination. In particular,
`computes` restricts heap access; transactional `Print` is not a heap permission
and remains available under the current output policy.

## Construction contracts (#508)

The pinned `Tests/Effects.versetest` supplies the heap default and inheritance
rules directly: empty unannotated types have the transacts budget; an empty
`class<transacts>` still requires all three heap permissions at its call site;
and a subtype must include the declared effects of its superclass and every
parent interface. A subtype may widen the budget. These requirements apply to
unused definitions too. A pure factory therefore declares its data type
`class<computes>` or `struct<computes>`, rather than relying on an empty body
to erase a default transacts contract. Existing pure-construction fixtures now
state that contract explicitly.

Source contracts are recorded after module resolution and before choice,
function-value and continuation generation. Each construction charges its
contract as well as the effects of the supplied fields, omitted defaults and
class blocks. All defaults are checked at their home type arguments, including
inherited interface defaults. Mutable fields and inherited unique identity
require allocation at the type definition, even when never instantiated.
Constructor functions keep their own declared effects; their expanded bodies
and selected delegations must include the data type's construction budget.

Compiler implementation types (function-value adapters, constructor field
packets and continuation frames) have no invented user construction contract.
They retain their existing operation-level checks. Constructing a source type
inside a generated helper still pays that source type's declared budget.
The same contracts survive generic instantiation, refining contexts and
receiver/function-value adapters; no Core or VM rule changes are needed.

These are **heap** contracts. The pinned `3582` tests separately restrict class
field initializers and permit effectful construction as an exception. This is
source evidence, not a released-engine execution result.

Initializer admission (#511) is checked independently, after implementation
helpers have been materialized. Every class/interface/struct field default is
checked at its declaration's opaque type arguments, including inherited homes,
unused definitions and imports. Ordinary source functions retain a private
provenance marker through lowering: calling one is refused even if its body
returns a literal. The checker follows compiler implementation calls and
constant aliases, so function-value/default/dispatch adapters cannot hide a
source call. It memoizes checked bodies and rejects recursive helper cycles.

Primitive expressions, finite Core `for` traversal and failure are separate
from divergence. A loop is accepted when its checked body cannot return an
ordinary value and repeat. `InitializerConvergence.mayNormal_of_eval` proves
that control-flow fact in the existing Core semantics; it admits finite
`first` lowering and single-iteration source loops without an execution-fuel
argument. Other loops have an explicit refusal boundary.

Construction blocks retain the Book's exception; their bodies have no new
termination assertion. Compiler-owned rational and ReplaceAll expansions
retain their finite intrinsic contract: Euclid/continued fractions decrease
absolute remainders, and replacement advances through a finite input. These
intrinsic implementation arguments are not a new general Lean termination
theorem. Source spellings or effect annotations cannot supply a trusted entry.
Existing Core safety, rollback and interpreter-agreement claims are unchanged.

`--extended-defaults` / `Options.extendedDefaults := true` explicitly select
the previous OpenVerse extension for ordinary computed/callback/spawn defaults.
Heap budgets and all caller failure/suspension/profile checks remain enforced.
Seventeen existing fixtures select that mode; heap/default and lexical-field
models select it only where they exercise the extension. Finite multi-value
selection and failable primitive defaults remain admitted by the checked mode.
Explicit `<converges>` remains refused in both modes. Data types still cannot
declare `<decides>` or `<suspends>`. Neither a heap budget nor compatibility
mode asserts termination, single-valuedness, output purity or engine behavior.

## Verification

After `lake build` and `make -C runtime`:

```sh
lake env lean --run tests/lean/EffectPolicy.lean
bash tests/scripts/test-effect-admission.sh
bash tests/scripts/test-construction-effects.sh
lake env lean --run tests/lean/InitializerConvergence.lean
bash tests/scripts/test-initializer-convergence.sh
```

The API contract covers direct AST input and all public source compiler entry
points, nested/default/leaf types, explicit entry expressions and generated
requests. The CLI suite checks 40 refusal fixtures through `check`, `core`,
`emit`, `run --emit` and the choice-free profile, with no execution/stdout and
no newly written or truncated bytecode. Every fixture has a tag-stripped
executable control with an independent output oracle, run in Lean and C;
unused imported variants check the same admission and source-file diagnostic.
Entry-expression and real missing-heap/callback-permission probes are included.
The suite currently reports 781 checks.

The construction suite independently enumerates all eight heap subsets for
class/struct call contracts, defaults in classes/interfaces/structs, and
class/interface inheritance edges. Empty types isolate declared permissions
from actual operations; unused definitions isolate definition checking from
reachability. It also checks default spellings, conflicting effects, mutable
and unique allocation, diamonds, imported negative cases with widened
executable controls, and generic/qualified/constructor/callback/choice paths.
It reports 1,411 checks across 581 cases. Four ordinary fixtures have explicit
Lean/C output oracles for initializer/block order, generic delegation and
escaping bound callbacks, choice helpers, rollback and cancellation cleanup.
Compiler API tests include explicit data contracts supplied in materialized
helper requests, as well as direct source/AST entry points.

The new ordinary fixtures exercise generic/default/interface/bound callback
calls, source-order rollback, choice continuations, refining casts and
cancellation cleanup. The full repository gate also retains the existing
effect, callback, GADT, source-context and scheduler models. Source annotations
are rejected before execution; no fuel bound is substituted for a static
termination claim, and no multiplayer behavior is inferred from the local VM.
