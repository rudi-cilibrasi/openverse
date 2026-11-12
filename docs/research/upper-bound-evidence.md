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
The pinned [Types chapter](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/11_types.md#void-and-false)
defines `void` as a universal discard supertype and `false` as empty bottom.

The parser retains the full bound type, including qualified, generic and peer
references. A declaration resolves its complete formal scope before validating
constrained applications. Its own facts justify those applications; facts from
an unrelated caller do not repair an unconstrained declaration. Type variables
remain opaque rather than being replaced by upper types.
Numeric refinements are also supported bound heads in the draft. Their implied
comparability propagates through peer bounds, alongside unique-class bounds.
Specializing a peer bound can produce a primitive or container upper type;
generated declarations retain and validate that type. Equality-preserving
comparable uppers imply comparability, while contextual discarding to `void`
does not establish that implication.

Executable conversion requires an actual value of the compiler-owned
`$subtypeEvidence(base,derived)` interface. Its `Up` method accepts `derived` and
returns `base`. A lexical name alone, a declaration fact, or a dummy type-value
witness cannot supply that value. Plans retain symbolic names, resolve current
slots at the use site, and only search visible bindings and compiler-owned
readonly proof fields. They do not walk arbitrary user object graphs.
A call result conservatively retains the dummy role when its callee or any
written argument carries that role, including ordinary generic forwarding
calls. This rule does not infer arbitrary function return dependencies.
Argument binding also refuses dummy inputs to executable proof and function
formals, including proof data exposed through containers or object fields.
This check uses the callee's declared domain. An unconstrained parametric
forwarder may still return metadata, retaining its role. Saved method receivers
and arguments keep their roles across dispatch; dummy receivers cannot execute
methods or function calls. Hidden `$w.` fields remain metadata.

The checked families currently cover:

| Relation | Executable evidence |
| --- | --- |
| Identity | Return the input at the same type. |
| Nominal class/interface ancestry | Check the ordinary upcast at exact projected arguments. Preserve source declaration constraints. |
| Transitivity | Compose actual dictionaries whose intermediate types match. |
| `int` to `rational` | Use the ordinary numeric embedding. |
| Numeric refinement widening | Use the shared interval-containment check to widen to the numeric base, a containing refinement, or the existing rational upper of an int refinement. Literal membership never establishes the reverse subtype relation. |
| Erasure to `any` | Evaluate the input before returning its erased representation. |
| Discarding to `void` | Evaluate the input before discarding it. Container conversions preserve their shape. This does not make every input comparable or permit a conversion back from `void`. |
| Bottom to any type | A checked `Up` body cannot return successfully. Its input must be evaluated first; errors and early exits propagate. Empty containers lift this relation without producing an element. |
| Arrays and options | Carry a real component dictionary. Preserve order and option absence. |
| Equal-arity tuples | Carry one real dictionary per component. Preserve shape and component evaluation order. |
| Nonempty tuple to array | Carry one real dictionary per component to the common array element type. Save the tuple once and project components in order. |
| Maps | Carry separate key and value dictionaries. Both key types must be comparable. Convert entries in order without reinserting them. |

Container proofs can be nested and composed with whole-value proofs. A supplied
`[]u <: []t` proof does not establish `u <: t`. The same rule applies to compound
relations retained by function-value adapters. Static entailment and executable
planning both retain this distinction.
Bottom retains its compiler-internal `$never` type and existing control-flow
representation. This work does not add a source spelling for the empty type or
give its erased Core representation an inhabited value. Both direct bottom
elimination and dictionary `Up` use existing checked error/control operations.

Tuple and tuple-to-array evidence is materialized once per arity. Nominal evidence is materialized
once per declaration pair, preserving generic parameters and constraints rather
than creating a new class for every closed instance. Missing declarations cause
compiler discovery/restart; discovery placeholders must not reach final Core.
Refinement evidence is materialized per source/result pair. Its ordinary `Up`
body uses the same interval helpers as concrete coercion. Those pure helpers
live below elaboration so static entailment and conversion share the rule.

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
Named defaults receive actual dictionaries for the callee's declared relations,
saved in fresh locals of the current call frame. The default keeps only earlier
parameters and these private proof names; unrelated caller source names stay
outside its scope. The final call reuses those saved dictionaries. Earlier
argument/default roles remain attached to their saved values, so a dummy
argument cannot become an actual default-scope proof.

Shared choice operations retain common method-local upper bounds in their
interface, forwarding function and implementations. Their typed probes require
actual lexical evidence and can infer parameters that occur only in a bound.
The operation identity includes the bound domain. Different per-case domains,
or relations that cannot be expressed on a retained binder, keep the checked
per-case source path rather than generating an unconstrained method.

Member lookup uses actual nominal views. Root and interior mutation preserve
the source storage type, evaluate indices/keys before traversal, and perform
each bound view after reading its source container. Augmented updates retain
their old-leaf read and their selected target across RHS mutation.

Inference retains precise input bindings. It can infer nominal projections and
common peer uppers, including component joins for matching containers. It does
not enumerate every Cartesian combination of tuple-component upper types.
Mixed tuples/arrays and different tuple arities can join through their common
element upper. Matching containers recurse only once per component; a second
array join at every nesting level would make deep inference exponential.
Comparable flags are intersected across equal type identities. Unrelated
interfaces can overlap; their ambiguity is not resolved by declaration order.
An explicit comparable constraint applies to that parameter. It does not
automatically make a lower peer comparable: the upper may be `void` and
discard a non-comparable value. Implied equality guarantees propagate only
from equality-preserving numeric, unique-class and component bounds. Tuple
adapters retain a whole-value relation without strengthening the original
components merely because the converted upper supports equality.
When inferring such an upper, calls, function values and inline instances
filter candidates by the upper's required kind. An available comparable upper
may be selected through actual bound facts without marking the original lower
type as comparable.
An invalid result-directed instance can retry from the original compiler state
using arguments/defaults, without changing explicit instances or runtime
argument evaluation.
Mutually equivalent candidate uppers use a stable type representative. In
particular, a mixture of `any` and `void`, including nested containers, must
not introduce inference ambiguity or depend on argument order.

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
(including function variance and full refinement/container
interactions), operation-dictionary and generated/opened/refined adaptation audits,
full construction/default/qualified-slot coverage, and a complete source
acceptance run. Context-sensitive literal coercion must not silently become a
general subtype fact. The final source contract, documented restrictions,
exact-head AI review and CI/full gate must all agree before the guard is removed
and the issue is closed.

The universal-bound regressions include `peer-void-comparable`, which preserves
a non-comparable class under a comparable peer instantiated as `void`, and
`peer-void-tuple-value`, which uses a `subtype(void)` identity as a tuple-taking
function value. Both have independent concrete controls. A negative refuses
equality on the original lower peer under only a comparable upper; the numeric
peer control verifies that equality-preserving bounds still allow equality.
