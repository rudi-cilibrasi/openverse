# Overloading conformance audit

Issue [#493](https://github.com/rudi-cilibrasi/openverse/issues/493), measured
against OpenVerse `c34adb6571f0703555922c83bba0756d98f5ebfc` (#499).
The [69-case matrix](../../tests/conformance/overloading/matrix.json) records
each source, classification, fixture and expectation: 28 accepted programs,
27 conforming refusals, one intentional entry-point restriction and 13 known
deviations. Accepted programs have exact output/status oracles and run in both
the Lean interpreter and C runtime. A refusal must have exit 4, the expected
diagnostic and no emitted bytecode.

## Sources and release evidence

The specification reference is the [Book functions chapter at
`beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/06_functions.md).
The same snapshot's [IndistinctOverloads tests](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/IndistinctOverloads.versetest)
give explicit callable/container and tuple/container declaration examples.
Its [development instructions](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/DEVELOPMENT.md)
identify the tests as copies of the compiler development suite and require
Windows VMs from `fortniteMain`. A pinned Book example establishes the
documented development rule; it does not establish that a released UEFN build
accepts it.

The released reference is **UEFN 38.00, November 1, 2025**, specifically its
published [entity/agent hierarchy and overload collision change](https://dev.epicgames.com/documentation/fortnite/38-00-fortnite-ecosystem-updates-and-release-notes?lang=en-US).
That release makes `agent` a subclass of `entity`, so overloads distinguished
only by those types collide. OpenVerse's
[related-class refusal](../../tests/errors/overload_subclass.verse) tests the
same rule with synthetic local classes. It does not import the Fortnite SDK
or run Epic's compiler. **No Epic engine runs were performed**; release
availability of the other Book examples remains unverified. This reference
is a specific published release rule, not a claim about the latest release.

## Supported calls and conforming refusals

The matrix contains individual fixtures; this table groups them by rule.
Links to `.verse` programs have adjacent `.expected` output/status oracles.
Negative fixtures state their expected diagnostic on the first line.

| Rule | Observed OpenVerse behavior and regression evidence |
| --- | --- |
| Primitive, class, enum domains and declared arity | [Selects a unique overload](../../tests/verse/overloading.verse); rejects [identical domains](../../tests/errors/overload_same.verse), [wrong arity](../../tests/errors/overload_arity.verse) and [no matching type](../../tests/errors/overload_no_fit.verse). |
| Generic inference | [Generic overloads](../../tests/verse/overloading_generic.verse), [nested calls](../../tests/verse/overloading_generic_nested.verse), [repeated parameters with subtyping](../../tests/verse/overloading_generic_subtype.verse) and [comparable bounds](../../tests/verse/overload_audit_comparable.verse) work; a [bare type parameter overlaps a concrete type](../../tests/errors/overload_generic_overlap.verse). Declared-arity selection here does not prove general upstream packing behavior. |
| Named parameters and defaults | [Required names distinguish overloads](../../tests/verse/overloading_named.verse), including [generic functions with defaults](../../tests/verse/overload_audit_generic_named.verse). [Name order](../../tests/errors/overload_named_order.verse), [default values](../../tests/errors/overload_named_default.verse) and an [optional extra name](../../tests/errors/overload_named_optional.verse) do not make overlapping overloads distinct; [missing required names](../../tests/errors/overload_named_missing.verse) are diagnosed. |
| Argument shapes | [Ordinary tuple-to-many calls and concrete array packing](../../tests/verse/tuple_args.verse) work. [Function-value adapters](../../tests/verse/fn_values_unflatten.verse) also pack explicit/generic tuples. An [explicit tuple versus the same flattened types](../../tests/errors/overload_tuple_flat.verse) is correctly refused. Ordinary and overloaded call gaps are listed below. |
| Written evaluation order | [Trace](../../tests/verse/overload_audit_named_order.verse): positional argument, named `B` then `A` as written, omitted `D` then `E` in declaration order, selected body once. The other overload's defaults never run. |
| Transaction boundaries | [Trace](../../tests/verse/overload_audit_rollback.verse): a failing suffix rolls back argument/default/body/suffix output and mutation; the retry evaluates each once. [Candidate effects](../../tests/verse/overload_audit_candidate_effects.verse) also leave an immediate pure overload usable without charging the discarded mutating overload. |
| Effects and suspends | [Selected writes are enforced](../../tests/errors/overload_effect_name.verse); [effects alone](../../tests/errors/overload_audit_effects_only.verse) do not distinguish declarations. [Immediate and suspending overloads](../../tests/verse/overload_audit_suspends.verse) coexist; [calling the selected suspending overload from immediate code](../../tests/errors/overload_audit_suspends.verse) is refused. Normal calls inside suspending code are allowed; `spawn` is not the only valid context. |
| Methods, inheritance and interfaces | [Override one/add another, super calls and dispatch](../../tests/verse/overloading_methods.verse), [declaration permutations](../../tests/verse/overloading_methods_permuted.verse), [transformed interface defaults](../../tests/verse/iface_default_copies_overloads.verse) and [implementation defaults through generic receivers](../../tests/verse/dispatch_defaults_overload.verse) work. [Overlapping inherited additions](../../tests/errors/method_overload_subclass.verse) are refused. [Sibling classes](../../tests/errors/method_siblings_not_overloads.verse) do not combine method sets. |
| Qualified implementations | [Separate interface slots](../../tests/verse/overloading_qualified.verse), [parametric interfaces](../../tests/verse/overloading_qualified_param.verse) and [mixed qualified/unqualified implementations](../../tests/verse/overloading_qualified_mixed.verse) work with OpenVerse's qualification syntax. [A qualified call with no matching slot](../../tests/errors/overloading_qualified_nomatch.verse) fails. These tests do not establish syntax equivalence with an Epic compiler. |
| Constructors | [Dispatch/delegation](../../tests/verse/constructors_overloaded.verse), [lexical defaults](../../tests/verse/constructors_overloaded_defaults.verse), [renamed generic parameters](../../tests/verse/constructors_overloaded_generic3.verse) and [selected effects](../../tests/verse/constructors_overloaded_effects.verse) work; [overlapping signatures](../../tests/errors/ctor_overload_same.verse) fail. |
| Empty values and class overlap | [Arrays](../../tests/errors/overload_arrays.verse), [options/logic](../../tests/errors/overload_option_logic.verse), [interfaces](../../tests/errors/overload_iface.verse) and [related classes](../../tests/errors/overload_subclass.verse) overlap. A [final non-implementing class versus interface](../../tests/verse/fuzz_3_overload_iface_vs_final.verse) and [disjoint instances of a generic class](../../tests/verse/fuzz_3b_overload_parametric.verse) are accepted. |
| Function domains and capture | [Different callback signatures](../../tests/errors/overload_audit_function_domains.verse) remain indistinct. Capturing an [overloaded function](../../tests/errors/overload_value.verse) or [method](../../tests/errors/fn_value_method_overloaded.verse) is forbidden by the pinned Book's capture rule. An [unambiguous method captured in an interface default](../../tests/verse/overload_audit_interface_value_scope.verse) retains that scope when the implementing class adds overloads. |

## Known deviations and implementation follow-ups

Each linked file is a complete minimal reproducer, except the deliberately
instrumented overloaded-tuple case, which also records the required
evaluate-once trace. Diagnostics below omit their source-location prefix;
the executable matrix checks the diagnostic text as well as status/output.
All upstream expectations in this table are Book/development expectations,
with released-UEFN availability unverified.

| Reproducer | Pinned expectation | Current observation | Follow-up |
| --- | --- | --- | --- |
| [Tuple / non-int-key map](../../tests/conformance/overloading/tuple_map.verse) | Admit `tuple(a)` versus `[logic]a`, explicit valid example. | Exit 4: `parameters a call cannot tell apart`. | [#500](https://github.com/rudi-cilibrasi/openverse/issues/500) |
| [Tuple / class option](../../tests/conformance/overloading/tuple_option.verse) | Admit `tuple(a)` versus `?a` for class `a`, explicit valid example. | Exit 4: same overlap diagnostic. | #500 |
| [Tuple / array](../../tests/conformance/overloading/tuple_array.verse) | Admit `tuple(a,b)` versus `[]a` for unrelated classes, explicit valid upstream test. | Exit 4: same overlap diagnostic. | #500 |
| [Flattened disjoint types](../../tests/conformance/overloading/tuple_flat_disjoint.verse) | Admit `tuple(int,int)` versus `(string,string)`; inference from flattening and disjointness, not a verbatim upstream test. Print `ints`. | Exit 4: same overlap diagnostic; differing element domains are ignored. | #500 |
| [Function / array](../../tests/conformance/overloading/function_array.verse) | Reject indistinct declarations, explicit upstream test. | Exit 0, prints `array`. | #500 |
| [Function / map](../../tests/conformance/overloading/function_map.verse) | Reject indistinct declarations, explicit upstream test. | Exit 0, prints `map`. | #500 |
| [Pack explicit tuple](../../tests/conformance/overloading/single_tuple_call.verse) | `F(3,"value")` supplies `tuple(int,string)`; print `value`. | Exit 4: `expected 1 argument(s), found 2`. | [#501](https://github.com/rudi-cilibrasi/openverse/issues/501) |
| [Pack empty tuple](../../tests/conformance/overloading/empty_tuple_pack.verse) | `F()` supplies `tuple()`; print `7`. | Exit 4: `expected 1 argument(s), found 0`. | #501 |
| [Pack generic tuple](../../tests/conformance/overloading/generic_tuple_pack.verse) | `Id(1,2)` at expected `tuple(int,int)`; print `1 2`. | Exit 4: `Id takes 1 argument(s), found 2`. | #501 |
| [Pack generic array](../../tests/conformance/overloading/generic_array_pack.verse) | `Count(1,2)` supplies `[]t`; print `2`. Inference from array packing and parametric rules. | Exit 4: `Count takes 1 argument(s), found 2`. | #501 |
| [Unpack overloaded tuple](../../tests/conformance/overloading/overloaded_tuple_unpack.verse) | Tuple argument selects the two-int overload, by the documented flattening rule. Print `pair 1`, `two 30`, `state 1`. | Exit 4: `expected string, found tuple(int, int)`; one-argument candidate selected before expansion. | #501 |
| [Class upper bound](../../tests/conformance/overloading/class_bound.verse) | `t:subtype(vehicle)` accepts and preserves `car`; print its `Doors` value `2`, as in the subtype-preserving Book example. | Exit 4: `unknown constraint subtype(vehicle)`. | [#502](https://github.com/rudi-cilibrasi/openverse/issues/502) |
| [Named function value](../../tests/conformance/overloading/named_capture.verse) | An optional-named function fits a zero-argument function type; call its default and print `7`, explicit Book example. | Exit 4: `has named parameters: such a function cannot be used as a value`. | [#503](https://github.com/rudi-cilibrasi/openverse/issues/503) |

The named-value case is **not** the overloaded-name capture restriction. The
Book's [named-parameter examples](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/06_functions.md#named-parameters)
retain required names in function types and allow eliding optional defaults.
OpenVerse currently rejects those values; the issue tracks the missing type
and adapter support rather than claiming an upstream ban.

Fixing these gaps must preserve receiver/argument/default evaluation order,
single evaluation, selected effects, rollback and cancellation boundaries.
In particular, accepting more signatures requires coordinated call adaptation;
removing overlap guards alone would admit declarations the caller cannot use.

## Intentional and unreleased boundaries

- [Overloading `Main`](../../tests/errors/overload_main.verse) is an intentional
  CLI entry-point restriction, not a demonstrated Verse defect.
- The pinned Book explicitly labels [nested functions](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/06_functions.md#nested-functions)
  unreleased. Their design is tracked separately in
  [#492](https://github.com/rudi-cilibrasi/openverse/issues/492); lack of local
  overload sets is not counted as released conformance failure here.
- This is an overload/call-boundary audit, not an exhaustive function grammar
  audit. Nested destructured/named tuple parameter syntax, extension method
  syntax and bottom-type expressions inside call arguments are not covered.
  No conformance result for those forms is implied. Multi-value call boundaries
  remain in [#283](https://github.com/rudi-cilibrasi/openverse/issues/283).

## Reproduce

After `lake build` and `make -C runtime`:

```sh
# The 56 existing-behavior/oracle checks; also part of scripts/check.sh.
bash tests/scripts/test-overload-conformance.sh

# Also measure the 13 deviations; write exact current observations.
bash tests/scripts/test-overload-conformance.sh --include-gaps --report /tmp/overloading.json
```

The audit command reports known deviations as `GAP`, never as passing
conformance tests. Matching an upstream expectation reports `RESOLVED` so a
future fix need not preserve the wrong behavior. An unexpected result,
unrelated diagnostic, missing/emitted bytecode at the wrong phase, or Lean/C
disagreement fails the audit. Known-gap reproducers live outside the ordinary
positive/negative golden suites; no golden asserts a wrong acceptance or
refusal as correctness. The JSON report preserves exact stdout/status/stderr
and explicitly records the absence of Epic engine runs.
