# Upper-bound source acceptance tests

`bash tests/scripts/test-upper-bound-source.sh` runs them, after building the
compiler; `scripts/check.sh` runs it. Every accepted program must pass the Core
checker and an independent output oracle in both Lean and C. Negative fixtures
require their specific bound or override diagnostic; an unsupported-feature
refusal does not satisfy them. The scope, input-role, operation, method-value
and callable contracts and compiler-API runtime artifacts are
`test-subtype-evidence.sh`'s.

Do not change an expected result to accommodate missing behavior: a positive
that fails is a defect, and a negative that a program now passes is either a
defect or a rule that changed, which its `.error` file and the rule's
documentation then say.

The FIFO cases have paired concrete controls. They check continuing rush-arm
ordering, captured method values and defaults, shared mutation, cleanup, and
precise generic results. The source owner stays alive through the signals and
final wait; its return would cancel the continuing arms. The sleep-only pair
also runs with the default scheduler. All FIFO and method-value positives must
produce identical bytecode with and without `--no-choice`. The callable-upper
positives require the same profile comparison.

The method-value pairs check contravariant arguments and covariant results
using real dictionaries, with escaping, once-only receiver, rollback and
cancellation oracles. The stored-function refusal pair records the existing
restriction on variance of already materialized function objects, independently
of class bounds. Reverse narrowing is refused separately.

The callable-upper pairs invoke opaque function values through actual bound
dictionaries. They cover defaults, precise returned values, receiver-before-
argument order, boxed callbacks, rollback, spawned tasks, waiting calls and
cancellation. Negative cases retain the ordinary bracket, suspension and
effect restrictions and refuse an unproved callable. The API contracts also
check callable-view ambiguity/order and dummy receivers through spawn.
The bound-only pair and API scans require function shapes mentioned only in
upper-bound metadata to be discovered and materialized, including generated
request headers and whole relations.

The container-view pairs use actual whole-container dictionaries for indexing,
queries, members and array methods. They retain precise generic results,
receiver/argument order, shared object references, rollback and waiting/task
cleanup. Interior mutation checks indices before traversal and old-leaf reads
before the RHS. A negative refuses writeback through an opaque container's
upper view; no inverse conversion or element relation is inferred. Empty
literal arguments are typed explicitly when the ordinary generic inference
rules cannot determine their precise type.

The main-integration pairs cover bounded method families that share a name
and proved member access inside refining failure contexts. A receiver counter
checks once-only evaluation across multiple results. The refinement pair also
requires identical bytecode in the choice-free profile.
