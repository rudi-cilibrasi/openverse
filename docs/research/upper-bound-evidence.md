# Checked upper-bound evidence (#502, draft)

Source upper bounds beyond `subtype(comparable)` remain rejected. This document
describes the implementation under development in #520 and its compiler-API
contracts. It does not announce source admission or completion of #502.

## Source contract and evidence

The development reference is the [pinned Book of Verse, Functions chapter](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/06_functions.md#type-constraints).
It describes bounds that expose upper-type members while preserving the precise
argument type, dependent bounds, and comparable constraints. Its
[variance section](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/06_functions.md#polarity-and-variance)
also describes covariance of both map keys and map values. These are pinned Book
development requirements; no released Epic engine or SDK was executed for these
contracts.

The parser retains the full bound type, including qualified, generic and peer
references. A declaration resolves its complete formal scope before validating
constrained applications. Its own facts justify those applications; facts from
an unrelated caller do not repair an unconstrained declaration. Type variables
remain opaque rather than being replaced by upper types.

Executable conversion requires an actual value of the compiler-owned
`$subtypeEvidence(base,derived)` interface. Its `Up` method accepts `derived` and
returns `base`. A lexical name alone, a declaration fact, or a dummy type-value
witness cannot supply that value. Plans retain symbolic names, resolve current
slots at the use site, and only search visible bindings and compiler-owned
readonly proof fields. They do not walk arbitrary user object graphs.

The checked families currently cover:

| Relation | Executable evidence |
| --- | --- |
| Identity | Return the input at the same type. |
| Nominal class/interface ancestry | Check the ordinary upcast at exact projected arguments. Preserve source declaration constraints. |
| Transitivity | Compose actual dictionaries whose intermediate types match. |
| `int` to `rational` | Use the ordinary numeric embedding. |
| Erasure to `any` | Evaluate the input before returning its erased representation. |
| Arrays and options | Carry a real component dictionary. Preserve order and option absence. |
| Equal-arity tuples | Carry one real dictionary per component. Preserve shape and component evaluation order. |
| Maps | Carry separate key and value dictionaries. Both key types must be comparable. Convert entries in order without reinserting them. |

Container proofs can be nested and composed with whole-value proofs. A supplied
`[]u <: []t` proof does not establish `u <: t`. The same rule applies to compound
relations retained by function-value adapters. Static entailment and executable
planning both retain this distinction.

Tuple evidence is materialized once per arity. Nominal evidence is materialized
once per declaration pair, preserving generic parameters and constraints rather
than creating a new class for every closed instance. Missing declarations cause
compiler discovery/restart; discovery placeholders must not reach final Core.

The container `Up` bodies use a private, typed elaboration form. It checks the
input/result shapes and every supplied dictionary type, then emits existing Core
loops, option tests, projections and ordinary dictionary calls. It introduces no
Core cast, opcode, runtime primitive, or map canonicalization. Inputs and proof
expressions are saved once. Ordinary concrete map coercion also supports checked
key widening so the concrete and generic contracts agree.

## Calls, captures and inference

The frame layout separates explicit arguments, actual proof arguments, hidden
type-value witnesses and receiver proofs. Receiver proof indices come from that
receiver's projected field layout. A caller's numeric slot never names a callee
proof. Helpers and their cache identities retain actual captures and type-value
roles, including source-context continuations and staged waiting consumers.

Defaults and retained inline metadata validate constraints even when a body does
not use its bound member. Method-local override bounds must match after class
projection and alpha-renaming; receiver constraints remain separate. Tuple
function-value adapters retain a complete substituted relation in readonly proof
fields and preserve parameters inferred only through bounds. They propagate
comparability only when the original relation implies it.

Member lookup uses actual nominal views. Root and interior mutation preserve
the source storage type, evaluate indices/keys before traversal, and perform
each bound view after reading its source container. Augmented updates retain
their old-leaf read and their selected target across RHS mutation.

Inference retains precise input bindings. It can infer nominal projections and
common peer uppers, including component joins for matching containers. It does
not enumerate every Cartesian combination of tuple-component upper types.
Comparable flags are intersected across equal type identities. Unrelated
interfaces can overlap; their ambiguity is not resolved by declaration order.
An invalid result-directed instance can retry from the original compiler state
using arguments/defaults, without changing explicit instances or runtime
argument evaluation.

Overload domains use each signature's own bound scope. Disjoint sibling-class
bounds can be distinguished, while ancestor/interface and empty-container
overlap remain possible. Direct capture of an overloaded name remains rejected,
following the pinned Book's
[Capture rule](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/06_functions.md#capture).
Bounded named wrappers may call those overloads and escape as values.

## Verification and remaining admission work

`tests/scripts/test-subtype-evidence.sh` runs scope/API contracts and exact
checked Lean/C artifacts. The container controls use ordinary concrete
coercions, independently of the new evidence plans. They exercise empty and
nested containers, multiple tuple arities, distinct key/value proofs,
once-only input evaluation, state, rollback, escaping method values, and
cancellation cleanup. Typed Core map producers also supply raw duplicate-key
entries; both paths must preserve their cardinality and order, including when
keys widen.

`tests/scripts/test-upper-bound-source.sh` is the development source acceptance
suite. It remains outside the ordinary gate while admission is guarded. To
measure progress, an isolated experimental checkout relaxes only that guard;
every positive still must pass Core admission, its exact Lean oracle and the C
oracle. A generic unsupported-feature diagnostic is not a correct negative
result. No admission bypass is published.

The existing Core checker and semantic proofs apply to the emitted Core under
their stated hypotheses. They do not prove that bound inference, dictionary
construction, capture provenance or frontend lowering implements Verse's source
semantics. Lean/C agreement is executable evidence, not that missing proof.

Before source admission, #502 still requires the remaining relation audit
(including refinements, bottom, `void`, tuple/array relations and function
variance), operation-dictionary and generated/opened/refined adaptation audits,
full construction/default/qualified-slot coverage, and a complete source
acceptance run. Context-sensitive literal coercion must not silently become a
general subtype fact. The final source contract, documented restrictions,
exact-head AI review and CI/full gate must all agree before the guard is removed
and the issue is closed.
