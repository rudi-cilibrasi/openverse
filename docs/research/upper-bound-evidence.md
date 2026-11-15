# Checked upper-bound evidence (#502)

Source upper bounds are admitted: a type parameter may be bounded by a class,
an interface, a parametric type applied, another type parameter, a numeric,
container or function type, `any`, `void`, `comparable` or
`castable_subtype(c)`. This document describes the checked evidence that
implementation rests on (built in #520, admitted in #502's last step), the
Book's rules it follows ([Rules](#rules-of-the-book-and-what-openverse-follows)),
and what stays refused, each by a rule of its own
([What stays refused](#what-stays-refused)).

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
Numeric refinements are also supported bound heads. Their implied
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
The source hint for a call conservatively retains the dummy role when its
callee or an ordinary value argument carries that role, including generic
forwarding calls. Declared metadata inputs, including compiler witnesses, do not taint an
independent real result. The flow analysis checks the actual return when a
callee returns a metadata formal. The source heuristic does not infer arbitrary
function return dependencies.
The flow analysis checks emitted arguments against executable proof and
function formals, including proof data exposed through containers or object
fields. The required inputs come from the callee's declared domain, before
substituting caller instances. Source argument hints no longer refuse a call
before the actual helper return is analyzed. An unconstrained parametric
forwarder may still return metadata, retaining its role. Saved method receivers
and arguments keep their roles across dispatch. Callable receivers are checked
on their emitted values, including a saved receiver with no concrete dispatch
implementation. A source hint may still describe a discarded input when a
conversion or a helper produces independent real data; that hint alone does
not reject the resulting real receiver or argument. Dummy receivers cannot execute methods
or function calls. Intrinsic task/event helpers require an executable receiver
too. Hidden `$w.` fields remain metadata.

Mutable storage also receives a compiler-only provenance check before failure
capture, shared-cell and concurrency lowering (#572). It follows local writes,
container updates, return values and opaque helper arguments to a fixed point
across branches, loops and recursive calls. A failed condition restores the
incoming roles. Locals declared inside a loop or for body start fresh each
iteration; cells already in scope retain their accumulated roles and storage
modes. A later real overwrite can clear an ordinary local's role;
metadata-only locals may still forward opaque values, including across a wait.
Evaluating a function or method receiver requires executable data even when
dispatch has no concrete implementation and lowers to an error expression.

Shared storage has a stricter boundary: metadata cannot enter an ordinary
object field or a shared local that has held executable data, even if that
local originally contained metadata. A real overwrite permanently ends its
metadata-only mode along that path; a failed condition restores the incoming
mode. Shared-storage mode checks run after recursive return summaries converge,
so an early real-only approximation cannot reject an opaque initializer that
later acquires a metadata role. The final pass follows calls from the roots
using converged summaries, excluding provisional argument contexts that are
no longer reachable. Checking the write protects every alias,
including aliases obtained by indexed reads or passed to an unannotated
helper. Compiler-owned `$w.` fields retain their
metadata role without tainting unrelated object fields. This analysis adds no
Core opcode or runtime tag. Generated getters of hidden fields also mark
their normal return as metadata, independently of the source member wrapper.
Opaque forwarding remains allowed, and reading an unrelated ordinary field
of an object with hidden metadata still gives executable data.
`MetadataGetters.lean` checks these accessor boundaries with 14 Core-checked
controls, including execution after forwarding through another function.
`MetadataStorage.lean` retains 104 real/dummy
rejection pairs and 100 opaque-forwarding, real-overwrite and rollback pairs,
including a later GADT refinement, fresh unit-to-array conversions, ordinary
helpers with independent real returns, virtual and spawned receivers, and
bound-method captures across a wait. Shared-frame controls cover metadata,
real data, then metadata writes while another arm waits to execute a function
or proof, plus recursive opaque initializers and rolled-back real overwrites.
`shared_function_overwrite.verse` executes ordinary real shared mutation in
both runtimes. Additional pairs cover direct, failable, recursive, named and
fresh-object returns passed to executable function or proof formals, retaining
both metadata refusals and independent real results. Module weak-map controls
cover direct, helper, nested, option and object payload writes; metadata cannot
enter ordinary shared fields, including unused, overwritten or rolled-back
writes. Real payloads produced by helpers with opaque metadata arguments
remain valid. Four pairs also check reads and writes from a running rush
arm's cleanup when a Signal resumes and ends its owner, including real
overwrites. Further controls retain the active continuation after an owner
return, including direct effects and cleanup installed after the Signal or
a completed rush. At its first suspension, cancellation validates the latest
cleanup; code only reached after that suspension stays unreachable.
Branches launched by that active step after the earlier cancellation drain
can currently survive in the runtime. The analysis records those launches
separately and retains their later effects after the owner's result is saved,
including delayed reads, writes, cleanup and descendant branches, and possible
later cancellation of a still-pending child. Their
metadata receivers and writes into real cells must still be refused; real
data remains valid. A child whose launch is only reached after the cancelled
arm's first wait stays unreachable. This follows the current runtime lifetime;
it does not change or establish that lifetime as an upstream requirement.
`metadata_module_functions.verse` and
`metadata_returned_arguments.verse` retain 25 ordinary runtime results in both
source profiles. These are
compiler-API contracts; source programs reach the same analysis.

Primitive result roles follow the payload returned by Core. Equality and
inequality return their left operand, so metadata in the comparison operand
does not taint a real returned object. An array index selects a payload
without entering it; array update combines the original array and replacement
roles. Every operand is still evaluated and its executable uses are checked.
The storage controls cover both operand orders, array comparisons, helper
returns and indexed reads/updates, including metadata executed inside an
otherwise discarded comparison or index operand.
`metadata_payload_operands.verse` preserves ordinary results and operand
effects in both runtimes and profiles. Typed-Core Signal dependency controls
also retain recursive indexed reads and updates: their receiver dependencies
include the array and replacement payload, excluding the scalar index.

For `sync`, `race` and `rush`, the provenance analysis follows source startup
order to determine which arms can start. An arm that neither returns nor
yields holds startup; an immediate race/rush winner also stops it. Unstarted
arms contribute no return roles or shared-cell effects. A waiting arm with
no normal return still lets later arms start. Started arms are evaluated
independently and exchange
possible roles and storage modes for cells already in scope until those roles
stabilize. Only writes performed by an arm participate in this exchange; an
unchanged or rolled-back cell cannot feed a sibling's role back as a new write.
Arm-local declarations start fresh. Per-arm effects join monotonically after
the first evaluation, so mutually writing cells cannot alternate their modes
indefinitely. Shared-mode diagnostics then use the stable
arm entries, preserving ordered metadata-to-real writes within one arm.

A successful `sync` completes every arm. Since metadata reentry is checked,
a cell definitely left real by one completed arm is real in the continuation.
`race` and `rush` retain possible roles from their arms because other arms may
still be waiting when a winner returns. `MetadataConcurrency.lean` checks 28
real/dummy rejection pairs and 34 forwarding/overwrite pairs, with Core checks
for every admitted case; `shared_function_sibling_writes.verse` executes the
ordinary real controls. These controls cover sibling order, nonreturning arms,
unimplemented dispatch, metadata-only forwarding, independent arm locals,
rollback and definite real overwrites.

Frames with potentially relevant background work or cancellation cleanup also
use a control-position analysis. `MetadataPlan` saves operand results before
calls and records continuations, fork startup and cleanup registrations.
Prefixes run atomically to a wait or completion. At a global wait, pending
children may resume against the current shared slots; a branch or surviving
rush loser cannot borrow the storage mode from its earlier launch point.
Returning stops pending background work before it can resume again. Cleanup
reads the current mutable cell, while a saved immutable alias retains its own
value. Structured children are canceled before their owner's cleanup, and
background branches after it, matching the suspension lowering.

Configurations with different pending work remain separate through conditions;
a failed condition restores its incoming slots. Loop back edges reset fresh
shared-cell modes and restore cleanup scope. Results from this analysis feed
the recursive return summaries, so forwarding an early background read through
a helper cannot erase its role. The final replay follows only live call
contexts. Functions without relevant scheduling sites keep the ordinary
dataflow path. Cleanup is relevant when its possible roles reach an executable
boundary, including effects in reachable helper contexts and their cleanup,
or it writes shared metadata storage. The relevance probe keeps those call
contexts private until the actual schedule makes them live. Forwarding hidden
witnesses alone does not require exploring schedules; scheduler model seed 18 retains
that distinction under the gate's unchanged 4 GB memory limit. No Core opcode,
runtime tag or scheduling behavior changes.

The scheduler exploration is conservative about the order of waits; it does
not prove timer deadlines. `metadata_background_timing.verse` retains ordinary
Lean/C traces for writes, cancellation, saved aliases and cleanup order in
both source profiles.

`Signal` also creates a scheduling boundary: matching event listeners are
detached in registration order and run to their next wait or completion before
the signaling caller continues. Timer waits and unrelated fresh events remain
pending. The analysis tracks event identities through local aliases, fields,
arrays and helper returns; uncertain aliases retain both possible schedules.
Concatenation collects element identities from each input array. Flattening
first follows the outer array to its rows, then follows each row to its
elements. Treating row identities as event or task identities can miss a
resumed metadata writer. The paired controls retain both matching and
fresh unrelated events through flattening, nested flattening and generic
helpers, plus event and task awaits. The ordinary fixture
`metadata_flattened_aliases.verse` preserves eight Lean/C trace results.
Successful equality and inequality comparisons retain the left operand's
object references through containers and generic helpers. Recursive Signal
summaries retain the same left-operand dependency, including argument
permutations; the four dependency contracts inspect checked Core programs.
The paired API controls cover mutations through returned receivers,
unrelated fields and rollback. `metadata_comparison_aliases.verse` preserves twelve
ordinary runtime results. Its no-swap recursive inequality control is also
retained in the dependency checks. Metadata admission for that control
remains a precision limit: the writable-recursion heap summary broadens
unrelated fields after conservative dispatch to sticky-event handlers.
The left-only dependency contract does not establish precise heap effects.
Function returns retain their heap state as well as the returned reference.
Conditionals, loops and for bodies accumulate returning paths separately from
fallthrough; a call joins the heap states of its normal and explicit returns.
This preserves writes performed before an early return and the fields of
fresh objects allocated on returning paths. Paired controls cover nested
helpers, returned receivers, condition effects, both returning branches,
unrelated events and rollback. `metadata_returned_heap_aliases.verse`
and `metadata_for_returned_heap_alias.verse` retain the ordinary runtime results.
Literal prototype references retain stable identities distinct from local
allocation sites. This includes the hidden module-state object holding
module-scoped weak maps. Its field reads include writes through possible
caller aliases; pre-existing contents remain possible caller objects rather
than arbitrary fresh allocations. Paired controls cover retrieved and saved
receivers, helper reads and writes, nested modules, unrelated events and
rollback. `metadata_module_aliases.verse` retains ten ordinary Lean/C traces
in both source profiles. Existing map contents and possible caller/prototype
aliases remain conservative: the API can still refuse a safe write through a
different holder while the ordinary executable trace remains valid.
Helpers that can wait or signal use distinct local slots in the control graph,
with their own metadata permissions, return targets and cleanup scopes.
A return in a surviving rush arm stops that arm after its group has ended;
returns from active groups still propagate to the owning function.
Recursive signaling helpers use a finite argument-dependency summary. Failed
conditions restore listener registrations, task states and caller storage.
Recursive calls that exclude heap writes preserve the identities already
stored in object fields. Their returned references remain unknown, and
writable recursive calls still widen fields. This keeps a pure recursive
calculation from turning a known unrelated event into a possible wakeup;
it does not infer a precise recursive return. The paired API controls and
`metadata_readonly_recursive_alias.verse` cover readonly calls, writable
calls and returned event aliases.
Task completion can wake a task awaiter during an event callback; cancellation
does not deliver a successful task result.

Repeated starts at a spawn site retain a conservative summary of older workers.
After those workers can progress, heap aliases widen and their possible signals
and task completions join the schedule; the caller's local storage is preserved.
This can admit extra schedules and reject safe programs. The exploration does
not establish complete alias or timing precision. Generated witness, capture
and frame aliases remain in the #572 audit, including resource use for recursive
choice producers. A private recursive-producer reader still reaches the 4 GB
cap on the #640 baseline and a bounded timeout with the frame-alias changes;
its real control passes. This remains an unresolved analysis case.
`MetadataSignals.lean` retains 47 real/dummy refusal pairs and 37 positive pairs
for direct and indirect signals, recursive helpers, rollback, task completion,
cleanup, helper returns and unrelated events. `metadata_signal_timing.verse`
executes the corresponding ordinary data paths in both runtimes and profiles.
`metadata_signal_loop_timing.verse` covers repeated spawns in the ordinary
profile, which admits `for`.

Borrowed mutable locals now retain their source-frame origins and recorded
synthetic copy-outs in provenance analysis. Inlining resolves each origin
against the active owner call, with distinct slots for separate calls of that
owner. Reads and writes use that cell's current role and storage mode. Synthetic
capture initialization does not overwrite the live cell; an ordinary immutable
copy keeps its saved value. This follows `SourceFrames` and `FrameRefs` without
changing emitted code. Generated borrowers are checked through their actual
callers rather than as independent source entries with stale capture arguments.
Provisional borrowed summaries defer executable checks; the inlined graph or a
live noninlined call performs them. Cleanup scopes retain the same aliases.
Readonly borrowers without escaping work retain the ordinary transfer when
their capture roles agree with the current owner. Borrowed writes select the
control graph when a shared cell or result can carry metadata; unrelated type
witnesses do not force ordinary data paths into schedule exploration. Stale
metadata captures also select the graph. Lifted background tasks first
undergo an executable-use probe; opaque witnesses alone do not select a
schedule. The probe records return-summary dependencies for invalidation.
Lifted branches and surviving
rush arms keep their source owner's task scope after a refining or default
helper returns; active structured groups retain their helper's lexical scope.
The owner cancels the background work, after its own cleanup. This distinguishes
an owner overwrite visible to a callback from a saved immutable copy.
`metadata_borrowed_signal.verse` retains ordinary Lean/C traces for a lifted
reader after a real overwrite, a recursive producer's write, two separate
owner calls, a surviving lifted writer, and owner-before-branch cleanup.

Return-summary solving records the summaries each context reads. A context
without cleanup is reused while those dependencies stay unchanged; the final
live replay still validates every reached context. Cleanup relevance probes
keep their existing private queues and bypass this cache. Scheduler exploration
also releases processed queue entries, retaining their joined configurations
in the fixed point rather than keeping every superseded copy.
Loop entry snapshots retain only shared-cell initialization and metadata modes,
which are the facts restored by back edges. Temporary values remain in the
current configuration; copying them into saved entries adds irrelevant joins.

A spawned call has a separate result boundary: lowering writes its return
value to the task's ordinary mutable `Result` field. The provenance check
inspects that return before the marker discards it, applying the ordinary
shared-field rule even if the task is never awaited. Passing metadata into a
task that returns independent real data remains allowed, as does opaque
forwarding within the task. A nonreturning task that may yield does not hide
its caller's continuation from validation. Return summaries also carry a
may-yield flag through reachable calls, branches and loops. Literal zero or
negative sleeps and nonwaiting helpers do not yield; starting a branch or
another task does not yield its owner. A branch releases its owner when its
child completes or first waits; an infinite waiting child cannot hide the
owner's later return or metadata use. A child that never returns or waits still
holds its owner. A race needs waiting paths in every
arm to yield, while a sync can wait for one arm after starting the others.
A task that neither returns nor yields holds its caller. Argument evaluation
and its exits still belong to the caller. `MetadataTasks.lean` checks these
boundaries with 17 real/dummy refusal pairs and 20 positive pairs, including
pairs for generic returns, helpers, aggregates, immediate results and discarded
tasks, plus independent real returns, argument effects and nonwaiting paths.

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
Ordinary members and intrinsic views participate in the same specificity
selection. A more-specific ordinary `worker.Await` must remain selected when
a redundant event proof is available; unrelated ordinary/intrinsic views are
ambiguous. Private API controls cover both proof orders and dummy ordinary
proofs. A source/control pair supplies the extra event proof through a constrained
holder's readonly field and checks ordinary computes calls with reversed argument
positions. This retains the distinction between a pure ordinary method and the
event's suspending intrinsic.
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

## Verification

The [acceptance matrix](upper-bound-acceptance.md) maps every #502 requirement
to the concrete artifacts that check it.

`tests/scripts/test-subtype-evidence.sh` runs scope/API contracts and exact
checked Lean/C artifacts. The container controls use ordinary concrete
coercions, independently of the new evidence plans. They exercise empty and
nested containers, multiple tuple arities, distinct key/value proofs,
once-only input evaluation, state, rollback, escaping method values, and
cancellation cleanup. Typed Core map producers also supply raw duplicate-key
entries; both paths must preserve their cardinality and order, including when
keys widen.

`tests/scripts/test-upper-bound-source.sh` is the source acceptance suite, and
`scripts/check.sh` runs it: every positive must pass Core admission, its exact
Lean oracle and the C oracle, and every refusal must give its own message; a
generic unsupported-feature diagnostic is not a correct negative result.

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

Source admission (the last step of #502) was measured before it was made:
with only the guard lifted, 151 of the 156 guarded acceptance cases passed as
they were (98 positives in Lean and C, 53 specific refusals) and the gate
passed but for one error test that expected the guard's message. The five
failures were fixtures that main's later rules had overtaken (a method named
as a top-level function a call could also fit, a `return` inside a returned
value, `tuple()` as the empty value's own type, a float oracle rewritten into
a string literal); and the Book's tests showed three rules openverse lacked
(below), which a bound had hidden behind the guard.

The universal-bound regressions include `peer-void-comparable`, which preserves
a non-comparable class under a comparable peer instantiated as `void`, and
`peer-void-tuple-value`, which uses a `subtype(void)` identity as a tuple-taking
function value. Both have independent concrete controls. A negative refuses
equality on the original lower peer under only a comparable upper; the numeric
peer control verifies that equality-preserving bounds still allow equality.

## Rules of the Book, and what openverse follows

The Book's prose (`docs/06_functions.md` "Type Constraints", "Member Access",
"Polarity and Variance"; `docs/10_classes_interfaces.md` "Advanced Type
Constraints"; `docs/11_types.md` "Where Clauses"; at the pinned revision) and
its tests (`Tests/`) agree on bounds wherever both speak; where the prose is
silent, openverse follows the tests. Cited by file and line:

- **What may be a bound.** A class (`ParametricFunctions.versetest` 31-110;
  prose ch. 6, 1381: `ProcessVehicle(V:t where t:subtype(vehicle))`), an
  interface (`ParametricTypes.versetest` 926), a parametric type applied
  (`Castable.versetest` 540: `castable_subtype(class1(int))`), `comparable`,
  another type parameter (prose ch. 6, 1410: `Convert(Base:t, Derived:u where
  t:type, u:subtype(t))`; `ParametricFunctions.versetest` 589 accepts
  `Foo(X:t where t:subtype(u), u:type):t`), and the metatype
  `castable_subtype(c)` (`Castable.versetest` 510-603; prose ch. 10, "A
  `castable_subtype` constraint goes further: it requires an argument that
  can be used as the target of a runtime cast"). openverse also takes the
  numeric, container, function, `any` and `void` uppers of [the
  table](#source-contract-and-evidence), which the Book's tests write only
  in `CompatibilityConstraints.versetest` 599 (`subtype(float)`,
  `subtype(int)`, in virtual packages the harness cannot translate).
  Several bounds on one parameter are refused by both (prose ch. 11, 521:
  "Using the same type in multiple constraints is not yet supported",
  its test 3588/3503/3532), and by openverse.
- **Member lookup** through the bound (prose ch. 6, 1414-1451: "you can access
  members that exist on the base type", `E.Name`, `E.GetStatus()`;
  `Castable.versetest` 547: `X.Value * 2` through `castable_subtype`).
- **Results at the argument's precise type** (prose ch. 6, 1367: "The function
  still returns type `t`, not the base type"; 1435: "`Info(0)` has type
  player"; `ParametricFunctions.versetest` 46-75: `F():class2 =
  AsClass1(class2{})` valid, `F():class2 = AsClass1(class1{})` and `F():int =
  AsClass1(class1{})` error 3510).
- **Inference and instances.** An instance outside the bound is error 3509
  (`ParametricFunctions.versetest` 36: `AsClass1(0)`; prose ch. 10, 1973:
  "ERROR: int is not a subtype of entity"; `Castable.versetest` 514, 586: a
  class that is not castable); an unbounded `t` passed where a bound is
  needed is 3509 too (`ParametricFunctions.versetest` 31), and a bound that
  implies the needed one is valid (`ParametricTypes.versetest` 1338-1351;
  prose ch. 10, 2019: a function taking a constrained class "has to repeat
  the constraint"). Type applications are checked where written, a type
  alias's included, used or not (`ParametricTypes.versetest` 639, 3509).
  A type parameter no parameter's type determines is error 3503
  (`ParametricFunctions.versetest` 336-374, 586). openverse applies that to
  bounded type parameters and those a bound names; for unbounded ones it
  keeps its documented reading that the expected result may give them
  (`docs/LANGUAGE.md`, "Readings"), which ~90 of its own programs rely on.
- **Overload distinctness.** Not pinned beyond the general rule
  (`ParametricFunctions.versetest` 332: `F(:t where t:type)` and `F(:int)`
  overlap, 3532). openverse treats disjoint sibling-class bounds as distinct
  and keeps interface, ancestor and empty-container overlap.
- **Variance.** Maps are covariant in keys and values (prose ch. 6, 1504;
  `ParametricFunctions.versetest` 580). A bounded generic function is a
  value only at a type whose parameter has the bound
  (`ParametricFunctions.versetest` 237-251: valid with `t:subtype(class1)`,
  3510 with `t:type`); openverse agrees.
- **Visibility.** A public parametric type's bound names nothing less
  visible (`ParametricTypes.versetest` 1284, 1294, 3593; the same snippets
  are valid under `?UploadedAtFNVersion := 3500`, a version gate openverse
  has no counterpart for).
- **Casts.** A value of a bounded type parameter is not cast directly
  (`Bugs/FORT-1059276.versetest` 10-15: `i[X]` with `X:t`,
  `t:castable_subtype(c)`, is 3509; 3-8: `Y:c = X; i[Y]` is valid).
- **Where prose and tests differ.** One place: the prose's
  `Convert(Base:t, Derived:u where t:type, u:subtype(t))` (ch. 6, 1410) is
  valid, while `ParametricFunctions.versetest` 134-145 keeps, commented out,
  tests of `u:subtype(t)` with the note "`subtype` doesn't support type
  variable argument". Commented-out cases are no tests; the live test 589
  accepts a bound naming a type parameter, as the prose does, and so does
  openverse (with evidence for `set C = B` of the commented test too).

## What stays refused

Each by its own rule and message, not by a blanket guard:

| Refused | Rule and why | Book |
| --- | --- | --- |
| an instance outside a bound | the bound's evidence cannot be made | 3509 |
| a bounded type parameter no parameter determines | its evidence must come from an argument's type | 3503 |
| a public parametric type with a less visible bound | a definition exposes nothing less visible | 3593 |
| several bounds on one type parameter | not supported, as in the Book | 3588 |
| `concrete_subtype(c)` as a bound | a class below a `<concrete>` one need not be concrete (`TypeValues`), so it is no subtype relation a bound's evidence can carry | (valid in `MetatypeConcreteSubtype.versetest` 49) |
| a cast of a bounded value, `i[X]` | upcast it first | 3509 |
| a cast to or construction of a type parameter, `t[X]`, `t{}` | no type value of `t` is passed (the prose's `dynamic_handler` in ch. 10 casts with `t[Item]`) | valid in the prose |
| a write through a container upper, `set X[0] = …` with `X:t` | no conversion back to `t` exists | not tested |
| variance of an existing function object | a bound adapts a method expression, not a function value already made (`method-value-stored-refusal`) | not tested |
| `subtype(t)` of a type parameter, as a value's type | types as values hold classes, interfaces and types written of types, not a type parameter (`types-as-values.md`); a type given as an argument, `F(t:type, X:t)`, and a bounded one, `F(t:subtype(c), X:t)`, are a type parameter whose argument the call writes since (`TypeArguments`) | valid (`ParametricTypes.versetest` 1305-1329) |

The castability of `castable_subtype(c)` is a subtype relation: a program that
writes such a bound has a hidden interface `$castableClass` above every
`<castable>` class and interface, so above the classes below them, and the
bound is the two relations `subtype(c)` and `subtype($castableClass)`, each
with its own checked nominal evidence (`UpperBounds.markCastable`).

