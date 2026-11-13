# The Readings table audited against the Book of Verse

The owner's rule is "for everything we go by the book for now": where the
pinned Book of Verse (its prose or its own tests) and an openverse reading
disagree, openverse changes to follow the Book. This note audits every row
of the table [Readings openverse takes](../LANGUAGE.md#readings-openverse-takes)
as it stands on main `7bf6dbd` (with #600, the empty value, and #601,
qualified names and the Book's shadowing rule), and the readings
that live elsewhere in [LANGUAGE.md](../LANGUAGE.md) which [the survey of the
Book's tests](book-test-conformance.md) names as contradicted.

The Book is the one the other notes pin, `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`.
Prose is quoted by file and line under `docs/` (the API reference is
`docs/api/verse_runtime_api.html`, a few very long lines; it is quoted by
line and entry), tests by file and line under `Tests/`. No Epic source code
was read. A case is "moved" when its verdict in `scripts/book-conformance.sh`
changes against the baseline of main `7bf6dbd`.

Verdicts:

- **agrees**: openverse does what the Book says.
- **Book silent**: neither prose nor tests decide; openverse keeps its reading.
- **contradicts the Book**: openverse changes, if the front end can make the
  change; otherwise the change is designed below and left for its own piece
  (Core, proofs, OVBC or the C runtime), or, when it is deeply load-bearing,
  designed with the list of what depends on the old reading.
- **the Book disagrees with itself**: its prose and its tests, or its tests
  among themselves, or its tests split by virtual machine. openverse does not
  change; both quotations are given for the owner ([For the
  owner](#for-the-owner)).

## The audit

| Reading | openverse (before) | Book prose | Book tests | Verdict |
|---|---|---|---|---|
| `int` range | 64-bit, overflow a runtime error (BPVM) | silent on the range; `04_operators.md:305` shows `BitShiftLeft[1, 64]` beyond 64 bits (VerseVM) | 26 `verse_vm_only` cases expect unbounded ints (`Operators/BinaryAddInt.versetest:35`, …); their `bp_vm_only` twins expect the runtime error | **VM-specific**: keep (owner list) |
| `X = Y` result | the left operand | `04_operators.md:58`: "`A = B` tests equality and returns a logic value"; `01_expressions.md:890`: "comparison operators return their left operand"; `08_failure.md:251`: "it returns its left-hand side" | `Operators/CompareMap.versetest:19` ("success returns LHS"), `CompareTypeChecking.versetest:8` (`return(a = b)` in an `:int` function), `CompareFloat.versetest:49-54` | **agrees** with the tests and most prose; ch. 4's "logic" is the dissent (owner list) |
| Associativity of comparisons | a chain checks every adjacent pair, result the leftmost | `01_expressions.md:890-891`: "comparison chains have special syntax that checks all adjacent pairs"; `:905-907`: "Verse does **not** evaluate … `A <= B <= C` as `(A <= B) <= C`"; `04_operators.md:50`: relational operators "Right"; `:40`: same precedence "evaluate left to right" | `Operators/Associativity.versetest:6-9`: "Test that `<>` is left associative", `assert{not 1 <> 2 <> 1}`; `:11-33`: `<`, `<=`, `>`, `>=` right associative (which, with the left operand as result, is the chain) | **the Book disagrees with itself** for `<>`; agrees for the others: keep (owner list) |
| Value of a successful `not e` | `void` | silent (`04_operators.md:466-473` gives "not P" as "Succeeds") | `Operators/LogicalNot.versetest:4-10` `(not false?) = false`; `Literals/Logic.versetest:72` applies `?` to it | **agrees** (the value is the empty value); `?` of it is the empty-value work's (#600, below) |
| Type of `if` without `else` | `void` | `01_expressions.md:600`: "The else clause can be omitted, though this affects the type"; not named | `FlowControl/If.versetest:842` refuses `123 + if (1 < 2): 42` ("type `void`"); `Return.versetest:146`: "they yield the value false" | **agrees** |
| A failing `for` body | the `for` fails | silent on the body (`08_failure.md:92` makes the domain a failure context) | `Option.versetest:118`: a failable body outside a failure context is 3512, so its failure is the enclosing context's; `for.versetest:352` passes either way | **agrees** (the tests imply it) |
| A failing `for` source | zero iterations for `X : F[]`; a failing range bound failed the enclosing context | `07_control.md:740-741`: "When any expression in the iteration header fails, that iteration is skipped" | `FlowControl/for.versetest:317` (range bound fails: `array{}`), `SoftwareTransactionalMemory.versetest` 74, 81 | **contradicts** for a range bound: **changed** |
| `?` on other values | only `logic` and `?t` | `08_failure.md:57`: "`?` turns any value into a failable expression"; `04_operators.md:384` and the API: `logic` and `?t` only | `Option.versetest:113`, `Array.versetest:112`, `Map.versetest:344` refuse `?` of int, array, map (3509) | **the Book disagrees with itself** (ch. 8 against ch. 4, API, tests); openverse follows the tests: keep (owner list) |
| Output inside a failed failure context | rolled back with the writes | chapters silent on the global `Print`; the API's `log` class (a different function): "If the transaction rolls back the lines are still printed, each prefixed with (Rolling Back)" | none (no test checks output) | **Book silent** on `Print`: keep; the `log` text noted for the owner |
| `Main` failing | exit 1 | no entry point | none | **Book silent** |
| `return` or `break` inside a failure context | leaves the function or the loop; what the context did is kept | `07_control.md:530-531`: `break` "must appear in a code block, not as part of a complex expression"; `:1067-1069`: `return` in "tail position" | `Bugs/SOL-4199-BreakFromIf.versetest` 4, 15, 51, 60 (`break` in an `if` condition, `for` domain, `option`, `logic`: 3658), 87 (`return` in an `if` condition: 3535); `FlowControl/Reachability.versetest` 12-15 ("Explicit return out of a failure context is not allowed"); `Return.versetest` 115, 118, 158-163 (in `<decides>` bodies, not in tail position) | **contradicts**, deeply load-bearing: **designed, not changed** ([below](#return-and-break-in-a-failure-context)) |
| Comparability | the row said every type but an unbounded type parameter | `04_operators.md:359-367` (comparable types; "Unique classes … identity equality only"); `11_types.md:195`: "A function value is not comparable"; `:225`: "`any` is not comparable" | `Operators/CompareInstance.versetest:11` (a class without `<unique>`), `Any.versetest:137`, `Map.versetest:50-58` | **agrees**; the row described openverse wrongly (it refuses classes without `<unique>`, interfaces, `any`, functions): row corrected |
| Inferring type arguments | first-order matching | `06_functions.md:1318-1320` (from the arguments), `:1358` (`t = []int via conversion`): no algorithm | `ParametricFunctions.versetest` 224, 229, 263, 269 agree | **Book silent** |
| Access specifiers | `<public>` and internal only | ch. 12 | 107 accepted refusals | not audited here: a later piece of its own |
| A qualifier without a `using` (#601's row) | `(M:)F` found as `M.F` | `10_classes_interfaces.md:1157-1160`: "A qualifier only says which `F` is meant among the ones already in scope; it does not itself bring anything into scope. Drop the `using` declarations and `(Top.M:)F(0)` … becomes an unknown identifier" | none listed by the row | **contradicts** the prose, as the row says; the qualified names' subject (#601), kept there (#145): not changed here (owner list) |
| A module's member used bare beside an outer name (#601's row) | the inner one | silent | `Modules/ModuleDefinitions.versetest` and the `vmodule` tests make both candidates (told apart by parameters, else ambiguous) | **contradicts** the tests, as the row says; #601's subject: not changed here |
| `ToString` of a float | the shortest round-trip decimal | `02_primitives.md:858`: `# Both produce: "Age: 25, Score: 98.5"`; the API (line 4555, `ToString(Val:float)`): "Fixed point with exactly six digits after the decimal point, always" | `Intrinsics/FloatToString.versetest` 15-24: `"1.000000"`, `"1234567890123456.000000"`, 1e100 in full | **contradicts** the API and the tests (the ch. 2 example dissents, owner list); needs the C runtime and Core's formatter: designed here, **changed** in `feat/core-book-primitives` ([below](#tostring-of-a-float)) |
| `NaN < X` | fails; `NaN = NaN` succeeds | `01_expressions.md:124-126`: `not (Nan < 1.0)`, `Nan = Nan  # But equality succeeds`; `02_primitives.md:378-379` | `Operators/CompareFloat.versetest:57, 58` | **agrees**; the row's "not stated" corrected |
| `=` between different types, `false` as a map, `X?` of a logic, `true` as a type | #600's | ch. 2 and ch. 4, as the rows quote | as the rows quote | #600's (equality and the empty value), not changed here; `false` as a map is on the owner's page already |
| Ordering of rationals | exact; an int compares with a rational | `04_operators.md:318-321` and the API declare `<` … for `int` and `float` only | none order rationals (`CompareRational.versetest` 5, 11 test `=`) | **Book silent** (the Book declares no ordering of rationals; no test refuses one): keep |
| Order of a choice's values | spatial | no choice `\|` in the chapters; `07_control.md:711-716`: nested generators give the cartesian product, leftmost outermost | `Operators/BinaryOps.versetest:3`: `a\|b` is a syntax error (3101, the code of syntax not yet supported) | **Book silent**: choice is an openverse feature from the Verse Calculus; keep |
| Code before a choice | runs once; alternatives rolled back in `if`/`first{}`; in a `for` only an alternative's own clauses | `08_failure.md:147`: "changes … are provisional—they only become permanent if the entire context succeeds"; `07_control.md:196-198` | none with a choice; for a `for` without one see [rollback of a `for` iteration](#rollback-of-a-for-iteration) | **Book silent** on choice; the `for` part is the rollback reading below |
| A choice in an operand of `and` or `or` | `A`'s clauses then `B`'s; `if (T := A) then T else B` | `08_failure.md:216-218`: `or` "tries each option in order, stopping at the first success" | none with a choice | **Book silent** |
| The three rows on functions with several values (#283) | as the rows say | silent (`yield` is not supported, `Yield.versetest:4-7`) | none | **Book silent** |
| Precedence of `\|` | below `+`, above comparisons | the precedence table (`04_operators.md:44-55`) has no `\|` | `BinaryOps.versetest:3` refuses `a\|b`; the commented-out `TimSyntax.versetest:280` puts `\|` below `:=` | **Book silent** |
| `Sleep(0.0)` | always yields, resumes next tick | `14_concurrency.md:1210`: "One frame, the smallest possible delay"; `:1227-1228`: "may resume in the same tick if no other work is pending"; the API (line 3939): "0.0 resumes on the next update and, crucially, does yield" | the tested example `14_concurrency.md:385-406` (`<!--versetest-->`): `Sleep(0.0)` "Completes at once, and wins" a `race` before a later arm begins | **the Book disagrees with itself**; the tested example contradicts openverse; the scheduler is the C runtime's and Core's: **designed, not changed** ([below](#the-scheduler-rows)) |
| `Sleep(S)` rounding | `Round(30·S)`, at least one tick | no tick rate; the API (line 3939): "a sleep resumes on the first update at or after its deadline and never sooner than the next one. Short sleeps therefore round up" | none | **contradicts** the API (it rounds up, openverse to nearest): **changed** in `feat/core-book-primitives` (the scheduler is Verse in the front end's prelude: [the rules](scheduler-conformance.md#the-books-scheduler-rules)) |
| End of a program with tasks | ends with `Main`; `Main` waiting on nothing is exit 2 | no entry point; `14_concurrency.md:829-832` leaves a task suspended at the end | none | **Book silent** |
| Order of a `subscribable_event`'s functions | subscription order; awaiters woken first, run after `Signal` returns | `14_concurrency.md:1606` (unreleased): listed in subscription order; the API (line 4341): "invoked in a randomised order on every signal"; line 4346: awaiting tasks "resumed first, in the order they suspended", line 4510: "Signal returns before the resumed tasks have finished" | `Event.versetest:27` (four `Signal`s in a loop all received: the awaiter runs inside `Signal`); `Bugs/BPVMOnly/RaceCompletionTiming.versetest` 65, 95 | **contradicts** (awaiters run inside `Signal`, before the code after it); runtime: **designed, not changed** |
| Event waiter resumption | scheduler order by default, `--event-fifo` suspension order | the API (line 4346): "resumed first, in the order they suspended"; `14_concurrency.md:1451-1452` "Each signal delivers one value to each awaiting task" against `:1486-1488` "each `Signal()` wakes exactly one awaiter" | `Coroutines/SpawnAndTask.versetest:318` (task awaiters in registration order) | **contradicts** the default (the API and the test); the chapter disagrees with itself on how many awaiters wake (owner list); runtime: **designed, not changed** |
| `Signal` in a failure context | allowed, rolled back by default | ch. 14 silent on `Signal`; the API (agent_group, line 1070): "Signal has the no_rollback effect, which a `<transacts>` function cannot call" | `Event.versetest` 83, 117 signal inside `<decides>` functions and must succeed | **agrees** with the tests (the API text dissents; owner list) |
| Extent of a `<#>` comment | the rest of the line and every deeper line | `00_overview.md:433`: "Indented comments begin with a `<#>` on its own line; everything indented by four spaces on subsequent lines" | `InterfaceWithFields.versetest:5` (3 spaces), `SoftwareTransactionalMemory.versetest:2` (2 and 4), `Roundtrip/Comments.versetest:309-334` (`<#>` after code) | **the Book disagrees with itself**; openverse follows the tests: keep (owner list) |
| Scope of `A and B` (a row on main before this work) | each operand its own scope | `07_control.md:1141-1142`: "`e0 and e1` evaluates the entire expression in a new lexical scope"; `01_expressions.md:840`: "Variable bindings do not escape from logical operations" | `Bugs/SOL-1830-LocalVariablesCanEscape.versetest:24-27`: "definitions in LHS is visible in RHS" | **contradicts**: **changed** |

The readings outside the table that the survey names:

| Reading | openverse (before) | Book prose | Book tests | Verdict |
|---|---|---|---|---|
| Order of `set X op= e` | the old value read before `e` (`set X += e` is `set X = X + e`) | `01_expressions.md:753`: `set Total += 1  # Equivalent to: set Total = Total + 1` (a pure right side); `:780-782`: the index once, "then reads that location, increments it, and stores the result back" | `ArrayAppend.versetest` 140, 183 (untagged), 7 and 12 (`verse_vm_only`): `e` runs first and its write is seen; `14_concurrency.md:465` (tested: `set Trail.Trace += FirstOneWins(…)` gives 102) | **contradicts** (the prose's equivalence is stated for a right side with no effect): **changed** |
| Key order of `ConcatenateMaps` | a key keeps its first position | the API (line 424): "the entries are laid down left first, then right, and a map keeps only the last value given for a key" | `Intrinsics/ConcatenateMaps.versetest` 21, 33; `Mutability.versetest:479` | **contradicts**: **changed** |
| Arity of `ConcatenateMaps` | one map or more | `03_containers.md:1029`: "It takes exactly two maps"; `:1040`: "To merge more than two maps, chain calls"; the API: `ConcatenateMaps(Lhs, Rhs)` | none call it otherwise | **contradicts** the prose: **changed** |
| Forward references between constants in one scope | allowed but cycles | silent | `Features/DefaultValueAssignment.versetest` 102, 128 ("can't refer to module variables that succeed them in the same module", 3502); 95-99 and `c22` allow another module's or an enclosing scope's | **contradicts**: **changed** |
| A module-level `X := e` states its type | required in a `module:`, not at a file's top level | `16_modules.md:149-150`: "All data definitions at module scope must also explicitly specify their type; type inference with `:=` alone is not allowed" | `Union.versetest` 23, 290 (`verse_vm_only`, at a file's top level: 3547) | **contradicts** at the top level: **changed** |
| `set M[k] = v` on a map can fail | never fails, allowed anywhere | the API (line 424): `operator'()'(Map:ref([t]u, [t]v), Key:t)…<decides>…`, "This is what makes `set M[Key] = Value` work on a map variable … Assigning through that reference inserts a key that is not yet present"; `03_containers.md:686`: "If you try to modify a key that is not present, the operation fails" (of `+=`); `05_mutability.md:344` (an array's index out of range fails); `01_expressions.md:994`: a `set` "returns the value being assigned" | `RollbackTortureTest.versetest:18` `(set Map[I] = I) or Err()`; `Mutability.versetest:248` `if (set M0[0] = 42)`; `Bugs/FORT-623803-STMRollbackAfterReturn.versetest:15` `if: set R[0] = R[0] or Err()` on a map; every map `set` in the tests is in a failure context | **contradicts**: a set through a map's key is `<decides>` (its last key still inserts); a plain variable's cannot fail; its value is the value set: **changed** |
| The left of `or` must be able to fail | not required | silent | `Operators/LogicalOr.versetest:143` ("the left operand is required to be fallible", 3513) | **contradicts**; with the map `set` failable the Book's own `(set Map[I] = I) or Err()` passes: **changed** |
| Rollback of a `for` iteration | a source's or a range bound's effects kept when later clauses fail | `08_failure.md:92`: "The `for` expression creates a failure context for each iteration of the domain clause"; `:147` (provisional changes) | `FlowControl/for.versetest` 362, 371, 392; `Range.versetest` 140, 159; `SoftwareTransactionalMemory.versetest` 88 (74 and 81 moved with the range bound) | **contradicts**, deeply load-bearing: **designed, not changed** ([below](#rollback-of-a-for-iteration)) |
| Commas and semicolons in blocks | `,` separates a block's statements like `;` | `01_expressions.md:1048`: "Commas within parentheses create *tuples*"; `:1153-1156`: `option{1, 2}?` is `(1, 2)`; `:1119-1129`: in a block "semicolons and commas are interchangeable as separators between definitions" | `SemicolonsVsCommas.versetest` 70 (`Value :=` then `1, 2, 3` is `(1,2,3)`), 95 (`{3,X}`), 100 (`option{1,2}`); `Option.versetest:44`; `for.versetest:293`; 22 parser cases (`TimSyntax.versetest:224` `"1,2"`, …) | **contradicts**: **designed and prototyped, not changed** ([below](#commas-in-blocks)) |
| What the Book calls warnings | code after `return`/`break`, `_` after a closed enum's every value, `return 3` in a `:void` function: accepted silently | `09_structs_enums.md:297-318`, `:411` ("⚠ Warning - unreachable wildcard"), `07_control.md:423-435` ("you'll get a warning") | `assert_semantic_error(2000)` (`Reachability.versetest` 5, 11, 23 "Treat unreachable expressions after break as warning not error"), 2302 (`Enum.versetest:356`), 2002 (`Return.versetest:179`, "produces a warning"): the runner counts a warning as a diagnostic | **contradicts** (a diagnostic the Book gives and openverse does not): **designed** ([below](#warnings)) |
| `break` in a `for` body | refused ("only inside loop (not for)") | `07_control.md:764`: "The `break` statement cannot exit `for` loops early" | `SOL-4199-BreakFromIf.versetest:38-48`: "`break` in a `for` body is allowed and breaks the surrounding `loop`" | **the Book disagrees with itself** (owner list); not changed |

## The changes

Each is one commit on `feat/book-readings`, in this order (least disruptive
first). "Moved" counts the Book's cases against main's baseline.

1. **`ConcatenateMaps` key order.** The later map's pairs replace the earlier
   one's at their own place: the result is the first map's pairs whose key
   the second lacks, then the second's (one `forE` and a `concat`, no new
   Core). Moved: `ConcatenateMaps.versetest` 21, 33 (different → agrees).
   Tests: `concatenate_maps(_more)` expected orders; the void-key case of
   `bound-concatenate-maps(-control)` keeps one pair (a map keeps one value
   per key). New: `concatenate_maps_order.verse`.
2. **`ConcatenateMaps` takes two maps.** Tests chain the calls; new
   `tests/errors/concatenate_maps_one`, `_three`.
3. **A failing range bound gives no iterations** (its and the other bound's
   effects rolled back, `orE` as for a failing source). Moved:
   `for.versetest:317`, `SoftwareTransactionalMemory.versetest` 74, 81.
   New: `for_range_bound_fails.verse`.
4. **An `and` is one scope**: `A and B` is elaborated as the block `A; B` (and
   lifted so with a choice), so `B` sees `A`'s names and neither escapes.
   No case moves (`SOL-1830` 26, 27 agreed by a refusal at another place).
   Tests rewritten: `errors/and_scope`, `errors/choice_and_scope` (now: the
   name is not visible after the `and`), `concurrency_prelude_and_scope_real_cast`
   (its real cast moved to the right of an `or`). New: `and_scope.verse`,
   `errors/and_scope_left`.
5. **`set P op= e` evaluates `e` before it reads `P`**: the indices and keys,
   then `e`, then `P`'s old value read and `P` rebuilt from what `e` left;
   with an object on `P`, after `P` has reached the object, whose values are
   read after `e`. A literal or a variable's value keeps the old code, as
   does an effect-free value where the read cannot fail. The choice lifter no
   longer saves the old value (`$withOld`), the heterogeneous write
   dictionaries take the new value first, and the mv model reads the old
   value after the right side, as does the rational fuzzer's model
   (`rational_arith.py`). Moved: `ArrayAppend.versetest` 7, 140, 183
   (12, `verse_vm_only`, keeps VerseVM's reference behaviour, `{{0}}`, with a
   TODO in the test itself). Tests rewritten to the Book's order (each now
   checks the new values): `choice_case_arms`, `choice_set`,
   `choice_expr_order`, `multi_frame_seq_lifted`, `multi_frame_seq_set_choice`,
   `rational_arithmetic_assignment`, `set_op_order_paths`, the 28
   `choice_dictionary_*` tests of compound writes, and
   `container-view-interior(-control)`: 37 in all. New: `set_op_order.verse`.
6. **A constant names only constants defined before it in its scope**
   (another module's or an enclosing scope's in any order). Moved:
   `DefaultValueAssignment.versetest` 102, 128. Test changed: `generics.verse`.
   New: `constant_order.verse`, `errors/constant_forward(_module)`.
7. **A top-level constant states its type**, as a module's already did.
   Moved: `Union.versetest` 23, 290. Tests given types: `type_or_value`,
   `type_aliases_forms`, `fn_values_param_signature`, `generics`, six
   `choice_waiting_default_method_*`; the generator `gadt_waiting_contexts.py`.
   A value openverse does not take yet that names a type, a scope or a
   module (`union{…}`, `scoped{…}`, `import(…)`, `subtype(t)`) is left to
   its own refusal. New: `errors/top_const_type(_value)`.
8. **A `set` through a map's key can fail**: refused outside a failure
   context, and its code says it can fail (`true?` after the insert, which
   succeeds), so an `if` may take it as its condition. Moved:
   `Mutability.versetest:248`, `FORT-623803-STMRollbackAfterReturn.versetest`
   22 and its definitions. Tests rewritten into failure contexts: `maps`,
   `generic_structs`, `iface_field_set_paths`, `concatenate_maps_order`,
   `mutation_tooling`, `choice_dictionary_map_plain`,
   `choice_dictionary_map_waiting` (waits first: a failure context cannot
   wait, ch. 13), `errors/choice_dictionary_map_immutable`, `_key_type`,
   and the "map update" contract of `tests/lean/MetadataStorage.lean`; the
   generator `gen-classes.py`. New: `map_set_failable.verse`,
   `errors/map_set_failure_context`, `errors/map_set_in_for_body`.
9. **The left of `or` must be able to fail.** Moved: `LogicalOr.versetest:143`.
   It refuses no test of openverse's; it refuses 282 programs of the frozen
   corpus, all from the mv model, whose `or` now wraps its left in a
   comparison that holds for every value it makes. New:
   `errors/or_left_cannot_fail`.

The programs whose bytes or output change are listed, each with its cause,
in [the survey's "After the readings audit"](book-test-conformance.md#after-the-readings-audit).

## Designed, not changed

### Rollback of a `for` iteration

**The Book's rule.** The tests fix it exactly: a `for`'s clauses, from one
success to the next, are one failure context with backtracking. Effects
made while searching for the next combination of the generators' values are
kept once a combination reaches the body (each success commits), and are
undone when the search ends with none; inside the search, a failing
alternative undoes back to its own choice point. `for.versetest:335`
(`for(I:=1..X.Inc(); I <> 1; S.QInc[])`, `X.V = 2`) keeps the source's
effect because a later element succeeds; `:362` undoes `Y.Inc()` of the
rejected `I = 2`; `Range.versetest:140` undoes the source's `set X` because
no element succeeds; `:159` undoes the bounds' effects for each rejected
`J`. openverse never undoes past a generator: what a source or a range bound
did stays.

**Design (front end, no new Core).** Core's `forE i src filt body` already
rolls back a failing filter; `ite` rolls back a failing condition. Lower a
`for` whose clauses have a generator after effectful code as a `loop` whose
step is `ite (search) (body; collect) (brk)`: `search` resumes the
generators from slots that hold, per generator, its source array and its
index; it advances the innermost generator, re-evaluating the inner sources
and the clauses in between, each alternative an `ite` of its own (so a
failing one undoes to its choice point), and fails when the outermost is
exhausted, so the `ite` undoes everything since the last success. A `for`
without effects before an inner generator keeps today's nested `forE`
(byte-identical), so the change is confined to programs the reading
affects.

**What depends on the old reading.** The `for` lowering in
`Front/Elab/For.lean` and its choice paths (#208 generators of `\|`, #235
multi-value calls taken lazily, #283 staged and refining continuations,
#314 exclusive choices, #417 staging), the [Choice](../LANGUAGE.md#choice)
row "Code before a choice" ("in a `for`, … only an alternative whose own
clauses fail is" rolled back), and the models that encode it:
`scripts/models/mv.py` ("a failure rolls back to the most recent
generator… effects of segments that succeeded are kept, even if later
generators give nothing"), `generic_mv.py`, `choice_break.py`,
`choice_heterogeneous.py` and `gen-choice.py`. Each must change first, then
agree with the compiler over a wide seed range. Cases that would move:
`for.versetest` 362, 371, 392, `Range.versetest` 140, 159,
`SoftwareTransactionalMemory.versetest` 88.

### `return` and `break` in a failure context

**The Book's rule.** A `return` may not leave a failure context (an `if`'s
conditions, a `for`'s clauses, `option{}`, `logic{}`, `not`'s operand, the
left of `or`; also a `<decides>` body anywhere but in tail position,
`Return.versetest` 158-163), and a `break` may not leave one for its loop
(`SOL-4199` 3658). openverse lets both leave, keeping what the context did
(#283 extends this through choices).

**Design.** A source check before elaboration (prototyped as `checkJumps`
in `Front/Elab/Source.lean`: two flags, a failure context since the
function's body and since the innermost loop, reset by `loop`), and the
tail-position rule for `<decides>` bodies. It is not made because what
depends on the old reading is large: it refuses 88 of openverse's own test
programs (73 in `tests/verse`, among them every `choice_clause_break_*`,
`choice_clause_return_*`, `choice_first_break_*`, `choice_first_return_*`,
`choice_block_defer_exits*`; 15 in `tests/errors`; 2 upper-bound controls),
302 programs of the frozen corpus (the generators `choice_break.py`:
`break-first` 71 and `break-for` 80; `gadt_first_returns.py` 20;
`gadt_immediate.py` 4; `mv.py`'s `bif`, `mv` and `rec` modes 125), and the
elaborator's paths for jumps out of failure contexts (#283's clause breaks
and returns, `$deferExits`, `forBreakSlot`, `forExitPacket`), which become
dead code. Making it is retiring those tests and models, removing those
paths, and rewriting the generators, a piece of its own. Cases that would
move: `SOL-4199-BreakFromIf.versetest` 4, 15, 51, 60, 87,
`Reachability.versetest` 12-15, `Return.versetest` 115, 118, 148, 158, 159,
161-163.

### Commas in blocks

**The Book's rule.** In a block, `;` and new lines make a sequence and `,`
makes a tuple: `{1.0, 2}` is a `tuple(float, int)`, `option{1, 2}` holds
`(1, 2)`, `Value :=` and the line `1, 2, 3` is `(1, 2, 3)`; definitions
joined by commas are the block's definitions (ch. 1's `X:int = 0, Y:int =
0`). `if (…)`, `for (…)` and the clause macros keep commas as clause
separators (ch. 1, `:1159-1174`).

**Design.** In the parser, a block's statement and the ones a comma joins to
it are a tuple (`parseStmtTuple`, prototyped), all-definition groups spliced
as statements; a comma at the start of a line that ends a nested block is
the enclosing list's (the prototype missed this, which broke
`gadt_refine`'s programs). A group mixing definitions and values needs one
more rule, which the Book's prose implies and no test pins: the
definitions visible to the later elements and after the group, so
`(V := X, V > 0, V)` is `V := X; T1 := V > 0; (V, T1, V)`.

**What depends on the old reading.** The generator `generic_mv.py`
(`option{V := …, E:[]w = …, set …, V(2) >= 7, V}`: 149 corpus programs),
and tests `class_cast_refine_for_choice`, `class_cast_refine_first_choice`,
`multi_method_own_direct`, `multi_method_cross_super_lazy`,
`multi_generic_mutual(_extra_types)`, `choice_immediate_suspends_refined_boundaries`,
which use commas as separators in `option{…}` or braces. Cases that would
move: `SemicolonsVsCommas.versetest` 70, 95, 100, `Option.versetest:44`,
`for.versetest:293` and the 22 parser cases.

### `ToString` of a float

**The Book's rule** (the API and the tests): fixed point, exactly six
digits after the point, every integer digit (`1e100` prints 101 digits),
`NaN`, `Inf`, `-Inf`, and a negative zero or tiny negative keeps its sign
(`"-0.000000"`). **Design:** the formatters are Core's (`Core/Float.lean`,
the shortest round-trip digits) and the C runtime's: replace both with
`%.6f`'s result (correctly rounded, ties to even on the exact binary value),
which C's `snprintf` gives and Lean can compute exactly from the double's
rational value; the float fuzzer's Python oracle becomes `'%.6f' % x`. Every
program that prints a float changes its output. Cases that would move:
`FloatToString.versetest` 15, 18, 19, 21-24.

**Changed** (`feat/core-book-primitives`). The rule, pinned exactly:

- *Six digits after the point, every digit before it.* The API
  (`verse_runtime_api.html:4555`, `ToString(Val:float)`): "Fixed point with
  exactly six digits after the decimal point, always: never scientific
  notation, never fewer digits, never more. … It is lossy —
  1.2345678901234567 prints as 1.234568 … It can be enormous — 1e100 prints
  as 101 digits followed by .000000, and the largest finite float as 309
  digits. And it collapses everything small — every subnormal prints as
  0.000000." The tests: `FloatToString.versetest:18` `"1.000000"`, `:19`
  `"1.500000"`, `:21` `"1.234568"`, `:22` `"1234567890123456.000000"`, `:23`
  and `:24` the exact binary values of `1e100` and `12.34e100` in full,
  `:25` the largest double's 309 digits, `:26` the smallest subnormal
  `"0.000000"`. The integer digits are the exact value of the double, not a
  rounding of it to 17 digits.
- *Rounding.* The Book states no rule for the seventh digit; its examples
  have no ties. openverse takes C's `%.6f` in the default rounding mode:
  the exact binary value rounded to the nearest multiple of 10^-6, a tie
  to the even last digit (`0.0078125`, which is 2^-7 exactly, prints
  `0.007812`; `0.0234375` prints `0.023438`). Python's `'%.6f'` gives the
  same, and is the fuzzer's oracle.
- *Signs.* The API: "The sign survives even when the digits do not, so a
  tiny negative value prints as -0.000000"; the test `:26`
  (`TestSignedFloatToString` of the smallest subnormal) expects
  `"-0.000000"` for its negation. A float with its sign bit set prints a
  `-`, also when every digit is zero. openverse has no negative zero (ch. 11,
  below), so `ToString(-0.0)` is `0.000000`.
- *Specials.* `NaN`, `Inf`, `-Inf` (the API; the tests `:16`, `:27`).
- *Interpolation.* `02_primitives.md:847`: "String interpolation implicitly
  calls `ToString()` on embedded values"; `:682`: "Interpolation works for
  any value that has a `ToString()` function in scope". `"{F}"` is
  `ToString(F)`, the same formatter, in openverse as before.

Lean computes the digits with integers from the bits (`VFloat.fixed6`: the
magnitude `m·2^e·10^6` rounded half to even by one division); C calls
`snprintf("%.6f")` (glibc's is exact and rounds in the current mode, ties
to even), into a buffer of 330 bytes (the longest result is 317). The
shortest round-trip rendering (`VFloat.render`) stays for the compiler's
own messages (a float literal named in a diagnostic). Moved: 7 cases,
`FloatToString.versetest` 15, 18, 19, 21-24 (different → agrees). Every
program that prints a float changes its output; see [the survey's section
for this work](book-test-conformance.md).

A new place where the Book disagrees with itself ([For the
owner](#negative-zero)): whether `-0.0` exists.

### The scheduler rows

The Book's tested ch. 14 examples and its API contradict three scheduler
readings, all the C runtime's and Core's: `Sleep(0.0)` completes at once
within a `race`'s first pass (`14_concurrency.md:385-406`; openverse
resumes it next tick); a `race`'s later arms do not begin once one
completes in the first pass (`:418-421`); an awaiting task runs inside
`Signal`, until it waits again, before the signaller goes on
(`Event.versetest:27`, API line 4510; openverse resumes it after the
signaller waits), awaiters in suspension order (API line 4346), and
subscribers after them in an order the API calls randomised. **Design:**
in the scheduler, `Signal` moves the event's waiters, in suspension order,
to the front of the run queue and runs them to their next wait before it
returns; `Sleep(0.0)` and `Sleep` of a duration that has already elapsed
complete without yielding when no other task is runnable at that point of a
`race`'s first pass; `Sleep(S)` rounds up to the first update at or after
its deadline. Each is a change to the proved scheduler model and to
`runtime/`, a piece of its own.

### Warnings

The Book's tests check three warnings with `assert_semantic_error`: 2000
(code after a `return` or `break`, or after a statement every path of
which jumps), 2302 (a `case`'s `_` after a closed enum's every value) and
2002 (`return` of a value in a `:void` function). They are warnings, not
errors: "Treat unreachable expressions after break as warning not error"
(`Reachability.versetest:22`), and the program compiles and runs.
**The smallest honest channel:** `openverse check`, `run` and `emit` print
each warning to standard error as `FILE:LINE:COL: warning: …` and go on,
the exit status unchanged; a program with warnings is still accepted. The
Book harness then reads an expected 2000, 2002 or 2302 as satisfied by such
a warning (not by a refusal). The checks are a reachability pass (a
statement after one that cannot complete normally: `return`, `break`, an
`if` whose branches all jump, a `loop` with no `break`, `sync` with a
jumping arm), and two checks the elaborator has the information for
(`case` arms against a closed enum's values; `return e` in a `:void`
function where `e` is not `void`). 30 accepted refusals of the survey's
"unreachable code" would agree.

## For the owner

Places where the Book disagrees with itself, in the form of [the wiki's
page](https://github.com/rudi-cilibrasi/openverse/wiki/Where-the-Book-disagrees-with-itself).

### Comparison chains with `<>`

- **Prose** (ch. 1, `01_expressions.md:890-891`): "comparison operators return their left operand when the comparison succeeds, and comparison chains have special syntax that checks all adjacent pairs"; `:905-907`: "Verse does **not** evaluate the comparison chain `A <= B <= C` as `(A <= B) <= C`. Instead, it is special syntax that checks both `A <= B` **and** `B <= C`". The precedence table (`04_operators.md:50`) says the relational operators are right-associative, and `:40` that operators of one precedence "evaluate left to right".
- **Tests:** `Operators/Associativity.versetest:6-9`: "Test that `<>` is left associative", `assert{not 1 <> 2 <> 1}`, which a chain (`1 <> 2` and `2 <> 1`) fails. For `<`, `<=`, `>` and `>=` (`:11-33`) the tests and the chain agree.
- **openverse today:** a chain for every comparison, so `Associativity.versetest:9` differs. A reading that satisfies both: chains for `<`, `<=`, `>`, `>=` ("range checking", `01_expressions.md:868-869`), `<>` and `=` left-associative.

### `ToString` of a float

- **Prose** (ch. 2, `02_primitives.md:853-858`): `Score := 98.5` … `# Both produce: "Age: 25, Score: 98.5"`.
- **API and tests:** the API's `ToString(Val:float)`: "Fixed point with exactly six digits after the decimal point, always"; `Intrinsics/FloatToString.versetest:18`: `"1.000000"`, `:22`: `"1234567890123456.000000"`.
- **openverse now:** the API's and the tests' (`98.500000`), in Core and the C runtime ([above](#tostring-of-a-float)); until `feat/core-book-primitives`, the shortest round-trip decimal (`98.5`), the prose's.

### Negative zero

- **Prose** (ch. 11, `11_types.md:691-694`): "IEEE 754 distinguishes between `+0.0` and `-0.0`. In verse Zero is just Zero, with no distinction between positve or negative. When any expression evaluates to Zero, the sign is discarded"; its tested example (`<!-- 30 -->`, `:696-712`) checks `-0.0 = +0.0`, which both readings satisfy.
- **API:** `prefix'-'(Value:float)` (`verse_runtime_api.html:404`): "A sign-bit flip, so negating zero genuinely produces -0.0 — a different bit pattern from 0.0, yet one that compares equal to it under Verse's extensional equality"; `ToString(Val:float)` (`:4555`): "a tiny negative value prints as -0.000000: a value that compares equal to 0.0 under Verse's extensional float equality yet prints differently from it", which only a negative zero can be.
- **Tests:** none negate a zero and print it (`FloatToString.versetest:15` prints `0.0` only, not through `TestSignedFloatToString`).
- **openverse:** ch. 11's: every float is canonical, `+0` for `-0` (DESIGN, "Floats: canonical bits"), so `ToString(-0.0)` is `0.000000`; a negative nonzero float too small for six digits prints `-0.000000`, as the API says.

### `?` on other values

- **Prose** (ch. 8, `08_failure.md:57`): "The query operator `?` turns any value into a failable expression. When applied to `false`, it always fails. When applied to any other value, it succeeds with that value." Against ch. 4 (`04_operators.md:384`, "checks if a `logic` value is `true`") and the API (`?` of `?t` and of `logic` only).
- **Tests:** `Option.versetest:113` ("unboxing non-options is an error"), `Array.versetest:112`, `Map.versetest:344` refuse `?` of an int, an array and a map (3509).
- **openverse today:** `logic` and `?t` only, as the tests.

### `X = Y`'s value

- **Prose:** ch. 4 (`04_operators.md:58`): "`A = B` tests equality and returns a logic value"; ch. 1 (`01_expressions.md:890`) and ch. 8 (`08_failure.md:251-252`): the left operand.
- **Tests:** `Operators/CompareTypeChecking.versetest:8` (`return(a = b)` in a function of `int`), `CompareMap.versetest:19` ("success returns LHS").
- **openverse today:** the left operand.

### The extent of a `<#>` comment

- **Prose** (`00_overview.md:433`): "Indented comments begin with a `<#>` on its own line; everything indented by four spaces on subsequent lines becomes part of the comment".
- **Tests:** comments indented 3 spaces (`InterfaceWithFields.versetest:5`), 2 and 4 (`SoftwareTransactionalMemory.versetest:2`), `<#>` after code (`Roundtrip/Comments.versetest:309-334`).
- **openverse today:** the tests' (every deeper line, any amount; after code too).

### `Sleep(0.0)`

- **Prose:** `14_concurrency.md:1210`: "`Sleep(0.0)      # One frame, the smallest possible delay`"; `:1227-1228`: "Unlike `Sleep(0.0)` which yields control and may resume in the same tick if no other work is pending"; the API (line 3939): "0.0 resumes on the next update and, crucially, does yield".
- **Tested example** (`14_concurrency.md:385-406`, a `<!--versetest-->` block): in a `race`, an arm `Sleep(0.0); 2` "Completes at once, and wins", and a later arm never begins.
- **openverse today:** always yields to the next tick (#156), so the example's race differs. Designed above.

### How many awaiters one `Signal` wakes

- **Prose** (ch. 14): `14_concurrency.md:1451-1452`: "Each signal delivers one value to each awaiting task"; `:1486-1488`: "If multiple tasks await the same event, each `Signal()` wakes exactly one awaiter—signals and awaits pair up one-to-one."
- **API** (line 4346): waiting tasks are "resumed first, in the order they suspended".
- **openverse today:** every waiter is woken (the first reading).

### `Signal` in a failure context

- **API** (agent_group, line 1070): "subscribable_event_intrnl.Signal has the no_rollback effect, which a `<transacts>` function cannot call"; line 1067: event delivery "is not un-run if the surrounding transaction later rolls back".
- **Tests:** `Event.versetest` 83 and 117 call `Signal` inside `<decides>` functions and expect success.
- **openverse today:** allowed and rolled back by default, as the tests; `--signal-no-rollback` gives the API's.

### `break` in a `for` body

- **Prose** (`07_control.md:764`): "The `break` statement cannot exit `for` loops early."
- **Tests:** `Bugs/SOL-4199-BreakFromIf.versetest:38-48`: "`break` in a `for` body is allowed and breaks the surrounding `loop`", which leaves the `for` too.
- **openverse today:** refuses a `break` in a `for` body ("break is only allowed inside loop (not for)").

### `set X op= e`

- **Prose** (`01_expressions.md:753`): `set Total += 1  # Equivalent to: set Total = Total + 1`, which, taken literally for a right side with an effect, reads `Total` first.
- **Tests:** `ArrayAppend.versetest` 140 and 183 run `e` first and see what it wrote; `:12` (`verse_vm_only`) and its native twin `:23-27` ("TODO (SOL-9022): This doesn't produce the same result as the non-native array. Either it should or we should runtime error") show VerseVM writing through a reference taken before `e`.
- **openverse now:** the tests' (`e`, then the old value read); `:12` still differs.

### Integer range, by VM

Already on the wiki page (entry 5).
