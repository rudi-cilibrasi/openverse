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
| `return` or `break` inside a failure context | leaves the function or the loop; what the context did is kept | `07_control.md:530-531`: `break` "must appear in a code block, not as part of a complex expression"; `:1067-1069`: `return` in "tail position" | `Bugs/SOL-4199-BreakFromIf.versetest` 4, 15, 51, 60 (`break` in an `if` condition, `for` domain, `option`, `logic`: 3658), 87 (`return` in an `if` condition: 3535); `FlowControl/Reachability.versetest` 12-15 ("Explicit return out of a failure context is not allowed"); `Return.versetest` 115, 118, 158-163 (in `<decides>` bodies, not in tail position) | **contradicts**, deeply load-bearing: **changed** ([below](#return-and-break-in-a-failure-context)) |
| Comparability | the row said every type but an unbounded type parameter | `04_operators.md:359-367` (comparable types; "Unique classes … identity equality only"); `11_types.md:195`: "A function value is not comparable"; `:225`: "`any` is not comparable" | `Operators/CompareInstance.versetest:11` (a class without `<unique>`), `Any.versetest:137`, `Map.versetest:50-58` | **agrees**; the row described openverse wrongly (it refuses classes without `<unique>`, interfaces, `any`, functions): row corrected |
| Inferring type arguments | first-order matching | `06_functions.md:1318-1320` (from the arguments), `:1358` (`t = []int via conversion`): no algorithm | `ParametricFunctions.versetest` 224, 229, 263, 269 agree | **Book silent** |
| Access specifiers | `<public>` and internal only | ch. 12 | 107 accepted refusals | not audited here: a later piece of its own |
| A qualifier without a `using` (#601's row) | `(M:)F` found as `M.F` | `10_classes_interfaces.md:1157-1160`: "A qualifier only says which `F` is meant among the ones already in scope; it does not itself bring anything into scope. Drop the `using` declarations and `(Top.M:)F(0)` … becomes an unknown identifier" | none listed by the row | **contradicts** the prose, as the row says; the qualified names' subject (#601), kept there (#145): not changed here (owner list) |
| A module's member used bare beside an outer name (#601's row) | the inner one | silent | `Modules/ModuleDefinitions.versetest` and the `vmodule` tests make both candidates (told apart by parameters, else ambiguous) | **contradicts** the tests, as the row says; #601's subject: not changed here |
| `ToString` of a float | the shortest round-trip decimal | `02_primitives.md:858`: `# Both produce: "Age: 25, Score: 98.5"`; the API (line 4555, `ToString(Val:float)`): "Fixed point with exactly six digits after the decimal point, always" | `Intrinsics/FloatToString.versetest` 15-24: `"1.000000"`, `"1234567890123456.000000"`, 1e100 in full | **contradicts** the API and the tests (the ch. 2 example dissents, owner list); needs the C runtime and Core's formatter: **designed, not changed** ([below](#tostring-of-a-float)) |
| `NaN < X` | fails; `NaN = NaN` succeeds | `01_expressions.md:124-126`: `not (Nan < 1.0)`, `Nan = Nan  # But equality succeeds`; `02_primitives.md:378-379` | `Operators/CompareFloat.versetest:57, 58` | **agrees**; the row's "not stated" corrected |
| `=` between different types, `false` as a map, `X?` of a logic, `true` as a type | #600's | ch. 2 and ch. 4, as the rows quote | as the rows quote | #600's (equality and the empty value), not changed here; `false` as a map is on the owner's page already |
| Ordering of rationals | exact; an int compares with a rational | `04_operators.md:318-321` and the API declare `<` … for `int` and `float` only | none order rationals (`CompareRational.versetest` 5, 11 test `=`) | **Book silent** (the Book declares no ordering of rationals; no test refuses one): keep |
| Order of a choice's values | spatial | no choice `\|` in the chapters; `07_control.md:711-716`: nested generators give the cartesian product, leftmost outermost | `Operators/BinaryOps.versetest:3`: `a\|b` is a syntax error (3101, the code of syntax not yet supported) | **Book silent**: choice is an openverse feature from the Verse Calculus; keep |
| Code before a choice | runs once; alternatives rolled back in `if`/`first{}`; in a `for` only an alternative's own clauses | `08_failure.md:147`: "changes … are provisional—they only become permanent if the entire context succeeds"; `07_control.md:196-198` | none with a choice; for a `for` without one see [rollback of a `for` iteration](#rollback-of-a-for-iteration) | **Book silent** on choice; the `for` part is the rollback reading below |
| A choice in an operand of `and` or `or` | `A`'s clauses then `B`'s; `if (T := A) then T else B` | `08_failure.md:216-218`: `or` "tries each option in order, stopping at the first success" | none with a choice | **Book silent** |
| The three rows on functions with several values (#283) | as the rows say | silent (`yield` is not supported, `Yield.versetest:4-7`) | none | **Book silent** |
| Precedence of `\|` | below `+`, above comparisons | the precedence table (`04_operators.md:44-55`) has no `\|` | `BinaryOps.versetest:3` refuses `a\|b`; the commented-out `TimSyntax.versetest:280` puts `\|` below `:=` | **Book silent** |
| `Sleep(0.0)` | always yields, resumes next tick | `14_concurrency.md:1210`: "One frame, the smallest possible delay"; `:1227-1228`: "may resume in the same tick if no other work is pending"; the API (line 3939): "0.0 resumes on the next update and, crucially, does yield" | the tested example `14_concurrency.md:385-406` (`<!--versetest-->`): `Sleep(0.0)` "Completes at once, and wins" a `race` before a later arm begins | **the Book disagrees with itself**; the tested example contradicts openverse; the scheduler is the C runtime's and Core's: **designed, not changed** ([below](#the-scheduler-rows)) |
| `Sleep(S)` rounding | `Round(30·S)`, at least one tick | no tick rate; the API (line 3939): "a sleep resumes on the first update at or after its deadline and never sooner than the next one. Short sleeps therefore round up" | none | **contradicts** the API (it rounds up, openverse to nearest); runtime: **designed, not changed** |
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
| Commas and semicolons in blocks | `,` separates a block's statements like `;` | `01_expressions.md:1048`: "Commas within parentheses create *tuples*"; `:1153-1156`: `option{1, 2}?` is `(1, 2)`; `:1119-1129`: in a block "semicolons and commas are interchangeable as separators between definitions" | `SemicolonsVsCommas.versetest` 70 (`Value :=` then `1, 2, 3` is `(1,2,3)`), 95 (`{3,X}`), 100 (`option{1,2}`); `Option.versetest:44`; `for.versetest:293`; 22 parser cases (`TimSyntax.versetest:224` `"1,2"`, …) | **contradicts**: **changed** ([below](#commas-in-blocks)) |
| What the Book calls warnings | code after `return`/`break`, `_` after a closed enum's every value, `return 3` in a `:void` function: accepted silently | `09_structs_enums.md:297-318`, `:411` ("⚠ Warning - unreachable wildcard"), `07_control.md:423-435` ("you'll get a warning") | `assert_semantic_error(2000)` (`Reachability.versetest` 5, 11, 23 "Treat unreachable expressions after break as warning not error"), 2302 (`Enum.versetest:356`), 2002 (`Return.versetest:179`, "produces a warning"): the runner counts a warning as a diagnostic | **contradicts** (a diagnostic the Book gives and openverse did not): **changed**, with the warning channel ([below](#warnings)) |
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

**Not built: the obstacle** (with the other three load-bearing readings,
[below](#the-load-bearing-readings-built)). The tests pin two more facts
the design must keep: the first generator's own source and the clauses
before it are inside the search (`Range.versetest:140`, `for (J:(set X =
array{666}); I := GetLower()..GetUpper())` undoes the `set`; `for.versetest:362`
undoes `X.Inc()` of the range bound), and an alternative of an outer
generator whose inner search finds nothing is undone before the next one
starts (`for.versetest:382`, "Only two increments since no values with I=2
reaches the body"). openverse's `for` is not lowered in one place: plain
generators are nested `forE`s; a choice is a generator of `altE`; a lazily
taken call (#246) is a private loop (`elabLoopGen`) that gives its values
one at a time with rollback boundaries of its own; an exclusive choice
(#314) has paths; a composed choice's clauses move into a continuation
(`$contf…`, #335); a waiting consumer is staged (#417, `$forStage`,
`$forPrepare`, `$forResume…`). Each commits a source and the clauses before
the next generator as it goes, and each needs the search with one
transaction per alternative; the models (`mv.py`'s rollback "to the most
recent generator", `generic_mv.py`, `choice_break.py`,
`choice_heterogeneous.py`, `gen-choice.py`) must predict it first.
Changing plain generators alone would leave a `for` over a choice under
the old rule, half the reading, so none of it is made yet.

### `return` and `break` in a failure context

**Built** (the second of the load-bearing readings, [below](#the-load-bearing-readings-built)).

**The Book's rule, as its tests pin it.** A failure context is an `if`'s
conditions, a `for`'s clauses (its domain), `first`'s clauses
(`08_failure.md:108`), `option{…}`, `logic{…}`, `not`'s operand, the left of
`or`, and a `<decides>` function's body (`08_failure.md:122`: "Functions
marked with `<decides>` create a failure context for their entire body").

- A `return` may not leave one (error 3535): in an `if`'s condition,
  `Reachability.versetest:12-15` ("Explicit return out of a failure context
  is not allowed") and `SOL-4199-BreakFromIf.versetest:86-95` ("`return` in
  an `if` condition is disallowed"); in `option{}`, `Return.versetest:129`.
  In a `<decides>` function it may be only in tail position:
  `Return.versetest:157`, "Explicit return can only occur in failure
  contexts in a tail position"; refused: `{return X; 0<>0}` (158),
  `{if(X<>0) {return X}; 0<>0}` (159), `{loop {return X}; 0<>0}` (162),
  `{for(Y:=0..X,X*Y=100){return Y}; 0<>0}` (163), an `else`-less `if`'s
  return as the body (148), `for(Y:=0..X){return array{0}; 0}` (115); valid:
  `return X` as the body (137), both branches of an `if` with an `else` as
  the body (160). Tail position, as read from these: the body's last
  expression, the last of a block in tail position, the branches of an `if`
  with an `else` in tail position, a `case`'s arms in tail position, the
  right of `and` and `or` in tail position, and a `return`'s value (140).
- A `break` may not leave one for its loop (error 3658): an `if`'s
  condition (`SOL-4199-BreakFromIf.versetest:3-12`, "`break` is not allowed
  in an `if` condition"), a `for` domain (`:14-30`), `option` (`:50-56`),
  `logic` (`:59-65`), `not` (`:67-71`), the left of `or` (`:73-77`); ch. 7,
  `07_control.md:530-531`: "The `break` statement must appear in a code
  block, not as part of a complex expression".
- Allowed: a `return` in a `for`'s body of a function that is not
  `<decides>` (`Reachability.versetest:18`, `Return.versetest:152`), in an
  `if`'s branch (`07_control.md:1065-1093`, the tested examples 46-48); a
  `break` in an `if`'s branch inside a loop; a loop's body is not a failure
  context, so a `break` there in a `<decides>` function stays (the Book's
  `SOL-4199-BreakFromIf.versetest:79-84` refuses a failable expression in a
  loop, 3512, a rule of its own openverse does not have). A `break` in a
  `for`'s body is where the Book disagrees with itself ([For the
  owner](#break-in-a-for-body)): the tests allow it (`:38-48`), the prose
  refuses it; the failure-context rule does not refuse it (a `for`'s body is
  no failure context), and openverse keeps its own refusal ("break is only
  allowed inside loop (not for)").
- Not this rule: 3534, a `return` as a strict subexpression of the value a
  function returns, explicitly or implicitly (`Return.versetest:110-133`,
  `F(X:int):int=X+(return 0)`): openverse accepts those still (with a
  warning, code never reached).

**What openverse does.** `checkJumps` (`Front/Elab/Source.lean`), a check of
the source before elaboration: a `return` with a failure context between it
and its function's body, or in a `<decides>` function anywhere but in tail
position, and a `break` with one between it and its loop, are refused.

**What it refused, and what went.** 84 of openverse's test programs had a
jump out of a failure context (none, of the Book's): 66 whose subject it
was (#283's breaks and returns in the clauses of first-success consumers
and of `for`s with choices, #246's returns after lazy generators, the
cleanup such a jump runs from a lifted block) are deleted, and 18 whose
subject is something else are rewritten to the allowed form, each with
its output unchanged (a `<decides>` function's early return as a branch of
its last `if`, a jump out of `not` or `option{}` moved to an `if`'s
branch). 14 error tests of how such jumps combine with other refusals are
deleted, one (`signal_no_rollback_break_clause`) rewritten; 11 new refusal
tests (`tests/errors/jump_*`) and `jumps_allowed.verse` are added. Of the
upper-bound fixtures, `bound-defer-exits(-control)` is deleted and
`bound-frame-cells-break(-control)` rewritten. The generators: `mv.py`
loses #284/#287's return among a test's clauses, `generic_mv.py` and
`choice_break.py`'s exclusive sources put a `<decides>` function's early
return in tail position, `gadt_first_returns.py` returns from the branch,
`gadt_immediate.py` loses its clause returns, and `choice_break.py` loses
its breaks among filters and first-success clauses (it models their
rollback, in a loop's body). 404 programs of the regenerated corpus are
refused (every one by this rule). The elaborator's paths that only such
programs reached are deleted (no allowed program's bytecode changed):
the `for`'s clause-break flag and its forwarding (`forBreakSlot`,
`forBreakCapture`, `$forClauseExits`, `forwardSourceBreak`), the break
packets of first-success clauses (`elabFirstGo`'s flag, `firstBreaks`), and
the return and break packets of first-success helpers (`firstResult`'s
exits, `firstUnpack`'s forwarding, `FirstLift.returnExit`/`breakExit`,
`FirstReturn`, the always-empty `normalResult` of `Choice.firstBody` and
`firstReturnBody`).

### Commas in blocks

**Built** (the fourth of the load-bearing readings, [below](#the-load-bearing-readings-built)).

**The Book's rule.** In a block, `;` and new lines make a sequence and `,`
makes a tuple: `01_expressions.md:1048`, "Commas within parentheses create
*tuples*"; `:1153-1156`, "In `option{}` constructor - follows the standard
sequence vs tuple rule: … `option{1, 2}?` … Comma: tuple, wraps the tuple";
its tests: `SemicolonsVsCommas.versetest:70` (`Value :=` and the line
`1, 2, 3` is `(1,2,3)`), `:91` (`F():tuple(float,int)={1.0,2}`), `:95`
(`for(X:=1..2){3,X} = array{(3,1),(3,2)}`), `:100` (`option{1,2}?=(1,2)`),
`:103` (`block{3.0,4}`), `:106` (`case(0){_=>{3.0,4}}`); `Option.versetest:44`,
`FlowControl/for.versetest:293` (`{Character,Index}`). Definitions joined by
commas in a block are its definitions (`:1119-1129`, "Within block
expressions (braces), semicolons and commas are interchangeable as
separators between definitions", `X:int = 0, Y:int = 0`); `logic{true?,
true?}` is valid (`:1140-1146`), as a tuple of two queries is. Separators
stay commas in clause lists (`for (X := 1..3, X <> 2)`, `:1159-1174`), in
the arms of `sync`, `race` and `rush` (`Reachability.versetest:98-108`,
`sync{F(0), F(1)}`), in a construction's fields and in collections' items.
A group mixing definitions and values: no test pins it; openverse reads it
as the prose implies, each element in order, a definition visible to the
elements after it and after the group: `(V := X, V > 0, V)` is `V := X;
T := V > 0; (V, T, V)`.

**What openverse does.** `parseStmtTuple` (`Front/Parser.lean`): a block's
statement and those a comma joins to it on its line are a tuple, a group
of definitions alone the block's definitions, a mixed group its
definitions and, for each value, a definition of its own, then the tuple
(a `var`'s value copied where it is defined). A comma that starts a line
is not the group's (the prototype took it, which broke `gadt_refine`'s
programs: it ends the block, and belongs to the list around it).

**What depended on the old reading.** The generator `generic_mv.py`
(`option{V := …, E:[]w = …, set …, V(2) >= 7, V}`, 53 programs of the
regenerated corpus) now separates those clauses with `;`, and so do the
tests `multi_generic_mutual(_extra_types)`, `multi_method_own_direct` and
`multi_method_cross_super_lazy`, each with its output unchanged (the others
the audit listed use commas where they stay separators). New:
`commas_tuples.verse`, `errors/comma_tuple_body`.

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

**Built** (the first of the load-bearing readings, [below](#the-load-bearing-readings-built)).

**The Book's rule.** Some diagnostics are warnings: the program compiles and
runs. The prose: `09_structs_enums.md:297`, "Adding one anyway triggers an
unreachable code warning" (a `_` after a closed enum's every value), and
its table at `:411`, "Closed | Full | Yes | Any | ⚠ Warning - unreachable
wildcard"; `07_control.md:423-424`, "If you add a wildcard when all cases are
covered, you'll get a warning that the wildcard is unreachable". The tests
name each with a code in the 2000s, checked by `assert_semantic_error`:
`FlowControl/Reachability.versetest:3` ("Test that a warning is produced
for unreachable code following a return"), `:22` ("Treat unreachable
expressions after break as warning not error"); `Return.versetest:177`
("explicitly returning a non-void value from a function with a void return
type produces a warning"). The codes the translatable tests name, and what
each is:

| Code | What | Cases (all warning codes) | openverse |
|---|---|---|---|
| 2000 | code never reached: after a `return` or `break` (`Reachability.versetest` 5, 11), after an `if` both of whose branches leave (11, 39), after a block that always leaves (57), after a `loop` that only a `return` leaves (76), the operation of an operand that leaves (91, `F(return)`), after a `sync` one of whose arms leaves (99, 100) or a `race`/`rush` all of whose arms do (107, 108); after a `case` all of whose arms leave (`Case.versetest` 272, 280) | 13, and with errors in 15 more | warns (`Front/Reachability.lean`) |
| 2002 | a `return` of a value in a `:void` function (`Return.versetest:179`; `:182`, `return F()` of a `void` `F`, is valid) | 1 | warns (the elaborator, with the value's type) |
| 2302 | a `case` arm never reached: `_` after a closed enum's every value (`Enum.versetest:356`, `Case.versetest:154`, `SOL-4194-…:20`), or after a union's (`Union.versetest` 175, 450, VerseVM-only) | 3 (and 2 of unions, which openverse does not parse) | warns (`elabCase`) |
| 2003, 2004 | `(a:)F()` in an override of `F`, where `(super:)F()` is meant (`SOL-3564-…versetest` 7, 18, 32, 45, 80) | 5 | not given: 4 still accepted silently |
| 2001 | an empty `defer:` (`defer.versetest:915`) | 1 | refused (agrees as an expected error) |
| 2017 | a map lookup that always fails (`SOL-6529-…versetest` 23-27) | 3 | refused for another reason |
| 2009 | a use of a `@deprecated` definition | 26 translatable | refused: attributes do not parse |
| 2005, 2007, 2008, 2011-2016, 2018, 2019, 2304, 2306, 2307 | versions, packages and their scopes | — | not translatable (`vpackage`) |

What is not reached, as the tests pin it: the code after an expression
that never completes normally, reported once where it starts.
`Reachability.versetest` 8-10, 18 (`for(x:=0..10){return x}; 1+2`: a
`for` may run its body no time), 98, 104, 105 (a `race` or `rush` with one
arm that leaves) and 113 are valid. Two things the tests leave open, which
openverse reads conservatively: a `loop` that nothing leaves, in a
`<suspends>` function (`Break.versetest:20`, `Coroutines/IteratedPrimitives.versetest:5`,
both `assert_valid`, have code after one): no warning (a `loop` that a
`return` leaves and no `break` does warns, `:76`); and an expression that
may fail before it leaves, in a failure context (`if (not (K = 2, return
42))`): the context's `else` is reached, so only the operation is
reported. The Book's `@ignore_unreachable` (`Reachability.versetest:94`) is
an attribute, which openverse does not parse.

**The channel.** `openverse check`, `run` and `emit` print each warning to
standard error as `FILE:LINE:COL: warning: …`, in the order of the source,
before anything else, and go on, the exit status unchanged; a refused
program prints its error alone ([FORMAT.md](../FORMAT.md), "Exit
protocol"). `scripts/test-verse.sh` compares a test's warnings with
`NAME.warnings` (none without one) and the rest of standard error between
Lean and C. The Book harness takes an expected error whose codes are all
warnings (2000-2999) as satisfied by a warning ("warned"; a refusal still
agrees, as for every expected error, the codes not compared), and notes a
warning where a case expects none (it does not judge it: the Book's runner
checks a warning's code only where a case names it).

## The load-bearing readings, built

After the nine changes above, the four readings this note designed and left
were built, one commit each (with work-in-progress commits inside the long
ones), in this order. "Moved" counts the Book's cases against the baseline
of the readings audit (7,390 agree, 2,066 refuse, 277 accept, 50 differ).

1. **Warnings** ([the rule](#warnings)). Moved: 17 cases agree (accepted
   silently before): `Reachability.versetest` 5, 11, 23, 39, 57, 76, 91, 99,
   100, 107, 108, `Case.versetest` 154, 272, 280, `Enum.versetest:356`,
   `SOL-4194-AssertOnMalformedCaseContainingDataDefinition.versetest:20`
   (2000 and 2302) and `Return.versetest:179` (2002). Tests: 18 of
   openverse's programs have code the rule finds never reached (each
   checked by hand: code after a `return` or `break`, after a `sync` one of
   whose arms returns, the tuple or map an operand's `return` leaves
   unmade), and say so in `NAME.warnings`; new: `warnings.verse`.
2. **`return` and `break` in a failure context** ([the rule](#return-and-break-in-a-failure-context)).
   Moved: 17 cases agree (accepted before): `SOL-4199-BreakFromIf.versetest`
   4, 15, 51, 60, 87, `Reachability.versetest` 12-15, `Return.versetest`
   115, 118, 148, 158, 159, 161, 162, 163.
3. **Rollback of a `for` iteration**: not built ([the obstacle](#rollback-of-a-for-iteration)).
4. **Commas in blocks** ([the rule](#commas-in-blocks)). Moved: 28 cases
   agree: `SemicolonsVsCommas.versetest` 70, 91, 95, 100, 103, 106,
   `Option.versetest:44`, `FlowControl/for.versetest:293`,
   `Bugs/2021-09-03-OptionalTupleAssertionFailure.versetest:3`,
   `v1-Mix-comma-and-semicolon-in-archetype-instantiation.versetest` 232 and
   `:decls`, and 17 parser cases (`TimSyntax.versetest` 72, 75, 220, 224,
   226, 229, 231, 242, 257, 264, 265, 268, 272, 275, 276, `Tuple.versetest`
   67, 70).

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
- **openverse today:** the shortest round-trip decimal (`98.5`), the prose's. The change is designed above (C runtime and Core).

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

### `break` as part of an expression

- **Prose** (`07_control.md:529-530`): "The `break` statement must appear in a code block, not as part of a complex expression."
- **Tests:** `SemicolonsVsCommas.versetest:97`: `assert{loop{1, @ignore_unreachable break}}`, a `break` as a tuple's element, expected to run (and `Reachability.versetest:91` takes `F(return)`, a `return` as an argument, with a warning).
- **openverse now:** the tests' (a `break` or `return` may be an operand, outside a failure context; the code after it is never reached, a warning).

### `set X op= e`

- **Prose** (`01_expressions.md:753`): `set Total += 1  # Equivalent to: set Total = Total + 1`, which, taken literally for a right side with an effect, reads `Total` first.
- **Tests:** `ArrayAppend.versetest` 140 and 183 run `e` first and see what it wrote; `:12` (`verse_vm_only`) and its native twin `:23-27` ("TODO (SOL-9022): This doesn't produce the same result as the non-native array. Either it should or we should runtime error") show VerseVM writing through a reference taken before `e`.
- **openverse now:** the tests' (`e`, then the old value read); `:12` still differs.

### Integer range, by VM

Already on the wiki page (entry 5).
