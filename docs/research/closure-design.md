# Nested functions and closures: proposed design

Planning for [#492](https://github.com/rudi-cilibrasi/openverse/issues/492),
part of #488. This is a proposal for a future implementation. Local function
declarations and lambda expressions remain unsupported in both source
profiles. No closure conversion or runtime change is included here.

## Sources and release evidence

The specification snapshot is the [Book functions chapter at
`beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/06_functions.md).
Its nested-functions section is marked unreleased; its lambda section says
arrow lambdas are unsupported. These are separate from the top-level and
bound-method function values OpenVerse already implements, including generic
instances and tuple adapters. The lambda section's advice to use nested
functions does not override the nested section's release warning.

The same snapshot's [NestedFunctions.versetest](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/NestedFunctions.versetest)
separates a Blueprint-VM link-error test from Verse-VM cases. It provides
development evidence for captures, state, recursion and restrictions, rather
than evidence that a released UEFN compiler accepts them.

Rechecked **2026-11-12**: the Book repository's current main is that same
snapshot. The published [Fortnite 43.00 release notes](https://dev.epicgames.com/documentation/en-us/fortnite/43-00-fortnite-ecosystem-updates-and-release-notes),
dated November 1, contain no announcement of nested functions or lambdas.
This absence is not an engine test or proof of unavailability. No versioned
UEFN compiler probe was run. Before calling either feature a released
conformance requirement, record the engine/compiler version, source,
diagnostics and execution result, and recheck the then-current documentation.

The remaining sections propose OpenVerse behavior using its existing
[function-value lowering](../DESIGN.md#function-values-hidden-interfaces-and-classes),
[effect admission](effect-conformance.md) and
[scheduler semantics](scheduler-conformance.md). Decisions beyond the pinned
Book's stated rules are proposal choices, not claims about Epic's compiler.
No lambda grammar is proposed; a future lambda feature needs its own source
specification and release evidence.

## Scope and binding

Use the Book's named local-declaration form, inside a function or an inner
block. Give every source binder an identity before generating helper names.
The declaration becomes visible at its declaration, with its own name
available in its body for recursion. Earlier enclosing parameters, locals
and local functions are visible; later declarations are not. Self recursion
is allowed; forward calls and mutually recursive local groups are refused.
Returning from the nested function returns from that invocation. A `break`
cannot target the creator's loop.

Apply the existing no-shadowing checks before renaming, including parameters
and class members. Local overloads may extend a preceding local overload
set under the ordinary overlap rules; each body sees itself and preceding
declarations, and later uses see the accumulated set. Keep the existing ban
on capturing an overloaded name as a value. Access specifiers, local class
definitions and `(super:)` inside a nested function are refused, following
the pinned nested-function restrictions. A method's nested function may
capture its receiver; it does not gain a new receiver or dynamic scope.

Check every nested body at its declaration, even when unused. Capture
analysis must include references in defaults, transitive nested captures and
types/witnesses, not just identifiers in the final expression. Preserve
declaration scope when checking defaults; evaluate a chosen default at the
call, in the existing argument/default order. Named function values remain
subject to [#503](https://github.com/rudi-cilibrasi/openverse/issues/503).

## Captures, state and lifetime

An immutable binding contributes its value to an environment. Capturing a
class reference preserves its identity and observes later field mutations;
it does not copy the object. Capturing an immutable aggregate follows the
same value semantics as ordinary assignment.

A captured `var` has **one shared location per execution of its binder**.
Promote that binding to a typed mutable cell. Rewrite all its accesses,
including accesses in the creator before and after the declaration, to that
cell. Sibling and descendant closures share it; different factory calls and
different iterations that execute the binder create different cells. A
closure formed in a loop over a variable declared outside the loop shares
that outer cell. Capturing the current contents separately for each closure
would be incorrect.

Store only needed values, cells, the receiver and type witnesses. Do not
retain a pointer to a Lean local, a C stack slot or an entire scheduler
frame. The environment and its cells have ordinary managed-heap lifetime:
an escaping closure can outlive its creator and other sibling closures.
Self recursion should pass the same environment to a code entry, without
constructing a self-referential environment for each recursive call. Existing
heap retention/reclamation limits still apply; this proposal adds no promise
of collecting unreachable cycles or bounded memory under infinite allocation.

Use the existing heap permission model for the proposed cells: creating a
mutable cell requires allocation permission; accessing its state requires
read/write permission as appropriate. Immutable environment construction
follows the existing function-value bridge rules. This is an explicit
proposal for promoted mutable locals, whose present uncaptured slot accesses
are not mutable heap accesses. Before adoption, test and document the effect
requirements at the source factory and nested body, rather than allowing
generated names or a pure-looking adapter to hide those charges. Do not
describe this permission choice as an upstream rule without evidence.

## Generic witnesses and effects

Retain the creator's instantiated type arguments and required runtime
witnesses in the environment, even if a witness occurs only in a captured
value or a nested signature. Preserve receiver refinements and bounds using
the existing typed interface/class machinery. Private generated names must
not let the caller's type variables capture the creator's. A local generic
function used as a value denotes one determined instance, following current
function-value inference; this does not introduce polymorphic function
values. Unsupported bounds remain diagnosed until their own implementation
([#502](https://github.com/rudi-cilibrasi/openverse/issues/502)).

Check the body's declared heap permissions, failure and suspension in its
lexical context. Forming a closure does not run its body or its defaults.
Invoking it charges the selected function's effects and evaluated defaults,
including through adapters, interfaces and generic callers. Preserve the
existing function-type effect subtyping. In particular, `<decides>` still
requires a failure context and bracket invocation, and `<suspends>` cannot
be erased by capture or invoked from an immediate context. Retain the
current effect-admission refusals for contracts the compiler cannot enforce.

## Rollback, cleanup and cancellation

Environments and cells are ordinary transactional heap values. A failed
failure context restores cell writes, closure-valued assignments, allocations
and output by the existing rollback mechanism. Every alias observes the
restored cell. An inner successful transaction remains provisional until its
outer context succeeds. Installing a new closure into an older object's
field in a failed context must not leave an escaping reference to discarded
allocation. No closure-specific side table may bypass the rollback heap.
Failure contexts still cannot suspend; rollback never spans a suspension.

A closure keeps values alive, not the creator's dynamic cleanup scope.
The creator runs its registered `defer` blocks when that invocation exits,
even if it returns a closure. A call of the closure owns its own defers;
they run once, last registered first, on that call's successful exit,
return or cancellation, under the current rules. Failure rolls back that
scope instead of running its defers. Storing a closure, copying its value
or reclaiming its environment does not register or execute a defer.

A suspending call gets its own continuation frame referring to the shared
environment. Its structured `branch`, `sync`, `race` and `rush` work belongs
to that invocation, using existing cleanup and cancellation order. Cancelling
a creator or one invocation does not invalidate an environment reachable
from another value or task, nor cancel another invocation solely because
they share cells. Cancellation runs applicable defers and retains prior
committed writes; it is not failure rollback. An escaped closure cannot
resume a cancelled invocation. Existing unstructured `spawn` and program-end
rules continue to apply.

## Implementation and adoption gates

1. Add a dedicated local-function surface node and lexical binder resolution.
   Validate scope, self recursion, overloads, defaults and effect contracts
   before transformations can erase declarations. Keep unsupported forms
   refused in both source profiles until all following gates pass.
2. Compute free bindings and mutable-cell promotion by binder identity.
   Generate module-level hidden environment classes and typed entry methods,
   then reuse `FnValues` shapes/adapters for calls and values. Generated
   classes do not authorize source-level local classes. Preserve positions,
   declaration scope, bound witnesses and source effect charges.
3. Lower to existing first-order Core; run `Prog.checkTypes` and existing
   compilation checks. Begin without new runtime opcodes or serialized raw
   pointers. If existing Core cannot express a case safely, revise the design
   and its proof/format boundary before admitting it. Existing Core proofs
   do not prove closure conversion correct.
4. Review source compatibility and the proposed permission policy, then run
   independent lifetime/state/rollback models against native execution and
   emitted bytecode in C. Add source rejection cases for bad scope, types,
   effects, escape and control transfer. Enable a documented subset only
   after these checks; update LANGUAGE and conformance tracking at that time.

The model must operate on bindings, locations, transactions and task events,
not on the generated hidden classes or interpreter output. At minimum:

| Model scenario | Required observation under this proposal |
| --- | --- |
| Factory at 3 returns getter/incrementer; increment twice after return; another factory starts at 10 | First getter yields 5, second yields 10; siblings share state, factory calls do not. |
| Shared state starts at 10; failed branch adds 2 and prints; successful retry adds 1 | State is 11; failed output is absent; successful effects occur once. Include inner success followed by outer failure. |
| Factory starts at 1, registers an exit defer adding 100, returns getter | The returned getter yields 101; retaining it does not delay or repeat the factory's cleanup. |
| Task publishes a getter of state 1, adds 2, then waits; its cancellation defer adds 20 | After cancellation another caller reads 23; cleanup runs once and prior writes remain. A separate invocation still works. |
| Generic factory returns a closure through a class/interface view and its creator exits | Calls preserve captured values, receiver identity and witnesses across concrete/compound types; incorrect bounds and effect conversions are refused. |

Also cover nested/transitive captures, repeated mutable binders in loops,
recursive calls sharing one environment, immutable object references with
changing fields, default evaluation order, suspending sibling calls, race
losers, task self-cancellation and failing allocations/closure publication.
Compare complete traces and exit status in both runtimes, with independent
expected outcomes, rather than using native/C agreement alone as the oracle.

## Current executable boundary

`tests/errors/nested_function_*.verse` cover indented, braced, parameterized,
method, unused and escaping mutable-capture declarations. The
`unsupported_arrow_*.verse` cases only assert rejection of arrow expressions;
they do not specify a future lambda grammar. They require exit 4 and the
current parser diagnostic through `scripts/test-verse.sh`. Those diagnostics
are generic syntax errors, not an implementation of lexical capture checking.
There is no opt-in closure flag.

Existing [function values](../../tests/verse/fn_values.verse),
[escaping generic bound methods](../../tests/verse/fn_values_method_instance_factory.verse),
[maps](../../tests/verse/maps.verse) and case fixtures are positive controls.
`=>` remains valid in map entries and case arms. A future diagnostic must
identify the unsupported expression context rather than ban that token.
The future runtime model matrix above is an adoption requirement, not a
claim that unsupported closures have already been executed or verified.
