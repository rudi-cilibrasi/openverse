# Upper-bound source acceptance tests

Run `bash tests/scripts/test-upper-bound-source.sh` after building the compiler.
Every accepted program must pass the Core checker and an independent output
oracle in both Lean and C. Negative fixtures require their specific bound or
override diagnostic; an unsupported-feature refusal does not satisfy them.

These are development tests for #502. They intentionally remain outside the
ordinary gate while `UpperBounds.checkParams` guards source admission. The
ordinary gate runs `SubtypeEvidenceScopes.lean` and the 26 compiler-API runtime
artifacts through `test-subtype-evidence.sh`.

Keep these acceptance tests failing until the requested source contract is
implemented. Do not add an admission bypass to the compiler or change the
expected results to accommodate missing behavior. Source integration can be
investigated in a separate experimental checkout with the guard relaxed there;
that does not establish readiness to enable bounds on the published branch.
