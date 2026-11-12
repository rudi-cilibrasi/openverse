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
Operation generation also retains the obligations of concrete receiver,
argument and result type applications. Generic operation interfaces,
forwarders and implementations keep these class bounds and their bound-only
dependencies; ordinary method, field and write operations retain them on each
implementation. Canonical identities include the retained class obligations.
Constructing a dictionary still requires actual current-frame evidence.
An unrepresentable class contract keeps the checked per-case source path.
Waiting environments retain actual captured relations as readonly proof
fields before their typed capture locals are initialized. This preserves
constrained dictionary types independently of capture order. Dummy captures,
mutable proof fields and declaration facts alone do not create these fields;
construction still supplies real dictionaries from the current frame.
Saved indexed-operation keys, objects, old values and right-hand sides also
retain their type-value roles. Four paired compiler-API controls require real
inputs to pass Core admission and refuse dummy inputs before the operation's
callee can consume their proofs. The key control reproduces the untagged
helper's admission of dummy executable evidence before this integration fix.

Method values with a fixed receiver can adapt their parameter and result
types through actual bound evidence. An argument conversion runs from the
expected parameter to the method's parameter; the result conversion runs
from the method's result to the expected result. The adapter stores the
required whole relations, including constraints on nominal type applications,
as readonly proof fields. Its private type parameters and identity include
those relations after renaming. Construction must supply real current-frame
dictionaries; declaration facts and dummy type values cannot create an
adapter. Whole-tuple proofs remain whole and do not imply component facts.

This preserves the existing distinction between adapting a method expression
and converting a previously materialized function value. The latter still
requires matching parameter/result types under the ordinary function-value
rules; a class upper bound does not introduce function-object variance.
`method-value-stored-refusal` and its concrete control document that baseline
restriction. The positive method-value controls cover escaping captures,
once-only receiver evaluation, mutation, rollback and cancellation.

An opaque value whose upper bound is a function type can be called through
that proved function shape. Selection uses actual lexical dictionaries and
prefers a unique nominal subtype, including the ordinary effect hierarchy;
unrelated callable views are ambiguous in either dictionary order. Static
facts or dummy dictionaries do not create a view. The checked `Up` call saves
the receiver once before its arguments. Arity, argument/result types, failure
brackets, suspension and effect checks then use the ordinary function-value
path. This does not create structural variance between function objects.

Spawn dispatch uses the same proved callable view and preserves the source
value's dummy role on its saved receiver. A dummy function or method receiver
cannot become executable through a generated spawn local. The input-role
controls cover ordinary and returned function values, method receivers, and
opaque callable values, with matching real controls. Source pairs cover
defaults, exact returned function types, receiver/argument evaluation order,
boxed callbacks, rollback, escaping tasks, waiting calls and cancellation.
Function-shape discovery includes upper bounds on functions, classes, structs
and methods, as well as retained generated-request headers and relations.
A shape written only in a bound must be materialized before type resolution;
an unrelated annotation or runtime call is not needed to make it available.

Concurrency intrinsics also require actual views: event/task `Await`, task
`Cancel` and zero-argument `Signal` on unit events have helper implementations
rather than ordinary method declarations. An opaque receiver can select one of
the same finite concurrency shapes that the concrete intrinsic admits. The
checked conversion and receiver are evaluated once before ordinary helper
lowering. Missing/static/dummy proofs and unrelated competing views remain
refused. Payload events do not acquire a zero-argument signal operation.
Ordinary suspension, defer and failure-context restrictions still apply.
Source/control pairs check event and sticky-event waits, precise task results,
once-only receivers, unit signals and cancellation cleanup. Admitted bytecode
stays identical in both source profiles and with `--signal-no-rollback`.
Separate direct and named-default controls retain legacy rollback signals by
default and require specific policy refusals in both profiles when the flag is
enabled. Checked dictionary conversion does not hide those calls from admission.

Member lookup uses actual nominal views. Root and interior mutation preserve
the source storage type, evaluate indices/keys before traversal, and perform
each bound view after reading its source container. Augmented updates retain
their old-leaf read and their selected target across RHS mutation.

Container operations also use actual whole-value views. Array/map indexing,
tuple projection, option/logic query, array/map `Length` and the ordinary array
methods run after a checked conversion of the receiver. Selection prefers a
strict subtype; mutually convertible uppers use a stable representative.
Unrelated applicable views are ambiguous. Equal view identities retain only
their common comparable guarantees, independently of dictionary order.
Declaration facts and dummy dictionaries cannot create an operational view,
and a whole-container proof does not establish an element relation.

Collection iteration consumes the same actual views for arrays, strings and
maps, including indexed and key/value generators. The source is evaluated once
before iteration, with its ordinary failure/rollback behavior. Array and string
concatenation convert opaque operands through actual whole-array proofs before
ordinary joining; the left operand still runs before the right. Generic element
types stay opaque. A whole-array upper does not authorize an unrelated element
type, and ordinary effect checks still apply to the iteration body.
Paired source cases check empty inputs, generic precise elements, map order,
Cartesian products, filters, aliases, rollback and waiting-loop cancellation.
Concatenation retains identical bytecode under `--no-choice`; collection
iteration remains excluded by that profile.

When ordinary concrete array joining fails, concatenation can infer a common
element upper from actual capabilities, including nested arrays and numeric
component conversions. An expected result is considered only when every input
has a valid executable plan; static declaration facts and dummy dictionaries
cannot repair missing proofs. At least one conversion must use an actual local
capability, so the fallback does not broaden ordinary unbounded joins. Unrelated
common interfaces remain ambiguous unless an explicit supported result selects
one. Whole-array proofs can convert whole inputs without establishing element
relations.

The `Concatenate` built-in also uses checked views. Its single-argument form
requires two array levels; component proofs and composed whole/component proofs
may supply the missing shape. Shallow views are discarded before selecting a
flattening view. The variadic form retains its ordinary first-array element type
and converts later arguments to that type. `ConcatenateMaps` uses whole map
views and, when an ordinary join fails, actual key/value capabilities for the
common map type. Conversion retains raw entry order; merging updates the first
matching key in place and appends new keys in argument order. Widening keys does
not silently canonicalize the converted first map. Paired source controls cover
precise elements, empty inputs, numeric keys, discard keys, once-only argument
evaluation, shared references, rollback, failure, escaping tasks and cancellation.
Both built-ins retain identical admitted bytecode under `--no-choice`.

Arithmetic operands can use actual integer, rational, float or numeric
refinement uppers. The checked conversion feeds the ordinary unary/binary
operators and `Abs`, `Min`, `Max`, `Floor` and `Ceil` paths. Integer division
retains failure on zero; float division and ordering retain their existing
NaN/infinity rules. Mixed int/float addition and reverse rational narrowing
remain refused. Numeric comparisons save the original left operand once,
compare converted values in order, and return that original precise value.
Chains preserve short-circuiting and do not evaluate later operands after a
failed comparison. Numeric proofs remain actual captures across waiting and
escaping task calls. Source controls check precise refinement results, operand
order, rollback, rejected division, cancellation and choice-free bytecode.
Ordinary `Abs` now widens a refined float to its base, as the other numeric
operators do; its concrete regression previously attempted an integer coercion.

Formatting also requires actual executable views. `ToString`, interpolation
and the command-line result printer consider only int, float, char, char32 and
string, including numeric refinements through their base. Composed component
proofs can turn a generic character array or tuple into a string; a whole-array
proof alone does not establish its missing character relation. Static facts,
dummy dictionaries and discard bounds do not authorize formatting. Unrelated
printable domains remain ambiguous. Already printable concrete inputs keep
their ordinary path, and rational/map/char32-array formatting remains refused.
Source controls check defaults, receiver proof fields, escaping method values,
operand order, rollback, failure, waiting and cancellation. The command-line
printer now prints char32/refined values that previously fell through; a
non-printable result still runs once without output. Four exact Lean/C entry
oracles and the new source pairs also require identical choice-free bytecode.

An interior write may traverse a container view to reach a mutable object.
The view executes during traversal, after index/key evaluation and after its
source container has been read. Writes that would rebuild an opaque container
through its upper view are refused: the conversion does not provide a checked
way back to the source storage type. Readonly fields and ordinary effect checks
still apply. Concrete controls check shared references, old-leaf reads before
RHS mutation, rollback, and containers retained by waiting/escaping tasks.
Empty option/array literals have explicit argument types where ordinary
generic inference cannot determine the precise instance; the unbounded
`Keep(array{})` control has the same inference restriction.

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
Structured generic arguments can also be inferred through actual views of
opaque inputs. Direct parameter matches retain the original precise type;
otherwise nominal projections and nested container patterns use real lexical
capabilities. Agreeing views share the inferred instance and its common
comparable guarantees; distinct inferred instances are refused. Ordinary,
inlined and method-local binding, including defaults, use the same rule.
After inference, a checked conversion consumes the once-elaborated argument;
the compiler does not reevaluate its source expression to obtain the view.
Parameters occurring only inside structural bound heads can collect lower-type
observations from arrays, options, tuples and maps. All incoming observations
and peer edges are collected before choosing a common upper; unresolved
compound dependencies defer that choice. Existing supplied bindings remain
fixed. Multiple opaque projections must agree, including their common
comparable guarantees. This only proposes an instance: it adds no component
facts, and the call must still supply evidence for every complete instantiated
relation. An empty tuple contributes no element instance.

The method-family and refinement integrations retain both subtype-dictionary
and method-family discovery results. A receiver's family is reported after
its proved view is resolved. Source/control pairs exercise bounded generic
families sharing a method name, a receiver evaluated once while yielding
multiple values, and actual evidence through refining option/boolean failure
contexts with state and rollback.
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

The [acceptance matrix](upper-bound-acceptance.md) maps every #502 requirement
to concrete artifacts and the evidence still needed for admission. The rows
are obligations, not a claim that the guarded draft has completed the issue.

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

The FIFO integration fixtures exercise rush-arm promotion before and after an
event signal, a rush inside a spawned task, multiple continuing arms, and a
sleep-only rush under both scheduler modes. Bounded and concrete versions
share independent state/order/cleanup oracles. The source owner remains alive
through the event signals and final wait; returning earlier would correctly
cancel its continuing arms. These cases also require identical bytecode with
the choice-free profile, as do the method-value adaptation controls.

The bounded recursive return-frame pair checks proof capture in recursive
suffixes, precise array element results, and bound-member reads before the
recursive call. The prefix runs once before recursion; rejected consumers undo
its output. The same pair checks rollback of a lazy branch's value-only `if`.
Its concrete version uses `car` directly and shares an explicit output oracle.
Return-frame snapshots also retain implicit lexical evidence, including
readonly proof fields whose names are absent from the written suffix. Snapshot
contracts require usable actual proofs and refuse dummy values, mutable proof
fields and static declaration facts.
The main integration also retains those captures when a shared continuation
forwards a clause break. A paired fixture carries a precise bounded value in a
shared recursive-frame variable, checks committed versus rejected cell writes,
and checks state copyback and cleanup on a composed-choice clause break.
Lifted-block defer exits retain actual evidence for their cleanup and precise
return values. A paired source control checks cleanup order and rollback of
rejected mutations on return and break. The private defer-exit wrapper keeps
the returned body's type-value role; a dummy mentioned only in a deferred body
does not taint an independent real result or create an executable proof.

The existing Core checker and semantic proofs apply to the emitted Core under
their stated hypotheses. They do not prove that bound inference, dictionary
construction, capture provenance or frontend lowering implements Verse's source
semantics. Lean/C agreement is executable evidence, not that missing proof.

Qualified-slot source controls retain two interface roots through a generic
constrained receiver, an override in a child class and an inherited qualified
implementation. They check alpha-renamed method bounds, named defaults, precise
returns, once-only receiver evaluation and mutation rollback; a strengthened
qualified override bound is refused. Construction/default controls check
earlier parameter values and their actual callee proofs, explicit field
initializers, receiver method defaults, omitted versus supplied arguments,
rollback and a receiver retained by an escaping task. These use the ordinary
initializer-convergence policy: constant field defaults remain strict, and
named parameter defaults do not acquire an unrelated convergence assertion.
They do not add sibling-field lexical scope to field defaults.

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
