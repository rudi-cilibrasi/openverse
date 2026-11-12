# Upper-bound source acceptance tests

Run `bash tests/scripts/test-upper-bound-source.sh` after building the compiler.
Every accepted program must pass the Core checker and an independent output
oracle in both Lean and C. Negative fixtures require their specific bound or
override diagnostic; an unsupported-feature refusal does not satisfy them.

These are development tests for #502. They intentionally remain outside the
ordinary gate while `UpperBounds.checkParams` guards source admission. The
ordinary gate runs the scope, input-role, operation, method-value and callable contracts
and compiler-API runtime artifacts through `test-subtype-evidence.sh`.

Keep these acceptance tests failing until the requested source contract is
implemented. Do not add an admission bypass to the compiler or change the
expected results to accommodate missing behavior. Source integration can be
investigated in a separate experimental checkout with the guard relaxed there;
that does not establish readiness to enable bounds on the published branch.

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
