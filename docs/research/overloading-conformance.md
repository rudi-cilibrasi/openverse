# Overloading conformance audit

Issue [#493](https://github.com/rudi-cilibrasi/openverse/issues/493), initially
measured against OpenVerse `c34adb6571f0703555922c83bba0756d98f5ebfc` (#499).
The [original audit](https://github.com/rudi-cilibrasi/openverse/blob/458f3974d2785c95ab25f2786496c0c8dfe49f1b/docs/research/overloading-conformance.md)
recorded 13 deviations. After #500 and #501, the [81-case matrix](../../tests/conformance/overloading/matrix.json)
tracks 42 accepted programs, 36 conforming refusals, one intentional entry-point
restriction and two remaining deviations. Eleven original cases now meet their
expectations, including overloaded tuple expansion. Accepted programs have exact output/status oracles and run in both
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
| Argument shapes | [Ordinary tuple-to-many calls and concrete array packing](../../tests/verse/tuple_args.verse) work. [Function-value adapters](../../tests/verse/fn_values_unflatten.verse) also pack explicit/generic tuples. An [explicit tuple versus the same flattened types](../../tests/errors/overload_tuple_flat.verse) is correctly refused; [disjoint flattened types and overloaded tuple expansion](../../tests/verse/overload_shapes_flattened.verse) work. Ordinary/generic tuple and array packing are covered by #501 and the call-packing fixtures below. |
| Written evaluation order | [Trace](../../tests/verse/overload_audit_named_order.verse): positional argument, named `B` then `A` as written, omitted `D` then `E` in declaration order, selected body once. The other overload's defaults never run. |
| Transaction boundaries | [Trace](../../tests/verse/overload_audit_rollback.verse): a failing suffix rolls back argument/default/body/suffix output and mutation; the retry evaluates each once. [Candidate effects](../../tests/verse/overload_audit_candidate_effects.verse) also leave an immediate pure overload usable without charging the discarded mutating overload. |
| Effects and suspends | [Selected writes are enforced](../../tests/errors/overload_effect_name.verse); [effects alone](../../tests/errors/overload_audit_effects_only.verse) do not distinguish declarations. [Immediate and suspending overloads](../../tests/verse/overload_audit_suspends.verse) coexist; [calling the selected suspending overload from immediate code](../../tests/errors/overload_audit_suspends.verse) is refused. Normal calls inside suspending code are allowed; `spawn` is not the only valid context. |
| Methods, inheritance and interfaces | [Override one/add another, super calls and dispatch](../../tests/verse/overloading_methods.verse), [declaration permutations](../../tests/verse/overloading_methods_permuted.verse), [transformed interface defaults](../../tests/verse/iface_default_copies_overloads.verse) and [implementation defaults through generic receivers](../../tests/verse/dispatch_defaults_overload.verse) work. [Overlapping inherited additions](../../tests/errors/method_overload_subclass.verse) are refused. [Sibling classes](../../tests/errors/method_siblings_not_overloads.verse) do not combine method sets. |
| Qualified implementations | [Separate interface slots](../../tests/verse/overloading_qualified.verse), [parametric interfaces](../../tests/verse/overloading_qualified_param.verse) and [mixed qualified/unqualified implementations](../../tests/verse/overloading_qualified_mixed.verse) work with OpenVerse's qualification syntax. [A qualified call with no matching slot](../../tests/errors/overloading_qualified_nomatch.verse) fails. These tests do not establish syntax equivalence with an Epic compiler. |
| Constructors | [Dispatch/delegation](../../tests/verse/constructors_overloaded.verse), [lexical defaults](../../tests/verse/constructors_overloaded_defaults.verse), [renamed generic parameters](../../tests/verse/constructors_overloaded_generic3.verse) and [selected effects](../../tests/verse/constructors_overloaded_effects.verse) work; [overlapping signatures](../../tests/errors/ctor_overload_same.verse) fail. |
| Empty values and class overlap | [Arrays](../../tests/errors/overload_arrays.verse), [options/logic](../../tests/errors/overload_option_logic.verse), [interfaces](../../tests/errors/overload_iface.verse) and [related classes](../../tests/errors/overload_subclass.verse) overlap. A [final non-implementing class versus interface](../../tests/verse/fuzz_3_overload_iface_vs_final.verse) and [disjoint instances of a generic class](../../tests/verse/fuzz_3b_overload_parametric.verse) are accepted. |
| Function domains and capture | [Different callback signatures](../../tests/errors/overload_audit_function_domains.verse) remain indistinct. Capturing an [overloaded function](../../tests/errors/overload_value.verse) or [method](../../tests/errors/fn_value_method_overloaded.verse) is forbidden by the pinned Book's capture rule. An [unambiguous method captured in an interface default](../../tests/verse/overload_audit_interface_value_scope.verse) retains that scope when the implementing class adds overloads. |

## Known deviations and implementation follow-ups

Each file in this table is a complete minimal reproducer. Diagnostics below
omit their source-location prefix;
the executable matrix checks the diagnostic text as well as status/output.
All upstream expectations in this table are Book/development expectations,
with released-UEFN availability unverified.

| Reproducer | Pinned expectation | Current observation | Follow-up |
| --- | --- | --- | --- |
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

## Tuple/container rules

Issue [#500](https://github.com/rudi-cilibrasi/openverse/issues/500) implements
this symmetric admission table; swapping the two types has the same result.
Here `D(a,b)` means their domains are known disjoint. `any`/`void`, opaque type
parameters, bottom and unknown refinements never supply disjointness evidence.
Refinements otherwise use their base, and `int` overlaps `rational`.

| Pair | Distinct exactly when |
| --- | --- |
| `tuple(ts)` / `tuple(us)` | Lengths differ, or some corresponding elements satisfy `D`. |
| `tuple(ts)` / `[]u` | Some element `t` of `ts` satisfies `D(t,u)`; an empty tuple overlaps. |
| `tuple(ts)` / `[k]v` | `ts` is nonempty and `D(int,k)`. Value types do not narrow this conservative map rule. |
| `tuple(ts)` / `?u` | `ts` is nonempty and `D(int,u)`. This extends the pinned singleton example conservatively to nonempty tuples. |
| Array / array, map / map, option / option | Never; each pair retains shared empty-value overlap. |
| Array / map, array / option | Never; retained overlap rules. |
| Map / option | Retained distinct domains. |
| Function type / array or map | Never, regardless of arity, effects, argument or result types. This does not enable a container-to-function conversion. |
| Function type / function type | Never, regardless of signature or effects. |
| Function type / tuple or option | Retained distinct domains, outside the pinned callable/array/map examples. |

The map-key and option-element `int` checks follow the pinned development
tests' boundary; open patterns that might instantiate to `int` still overlap.
The tuple/array test needs only **one** distinct element, as the upstream test
states; requiring all elements to be distinct would refuse valid tuples.
Pairs marked retained are preservation of existing OpenVerse rules, not an
additional released-UEFN conformance claim. Class/interface overlap is unchanged.

A single explicit tuple parameter compared with several positional parameters
now compares their element domains, rather than only equal flattened arity.
If a tuple argument does not fit a one-argument overload, the existing tuple
expansion retry can select the flattened overload. Receiver evaluation precedes
the tuple producer, each runs once, and names/defaults retain their usual order.
[Selected effects and call syntax](../../tests/verse/overload_shapes_selected_effects.verse)
are checked on the overload reached after expansion; a discarded suspending or
failable candidate cannot block it. [Errors inside the producer](../../tests/errors/overload_shapes_producer_error.verse)
remain errors rather than being discarded by retries. Deeply nested invalid
producers also have timed refusal checks, so retries cannot repeatedly traverse
their errors. Failed expansions preserve the original diagnostic.

Resolved original cases retain their reproducers and historical observations in
the matrix: [tuple/map](../../tests/conformance/overloading/tuple_map.verse),
[tuple/option](../../tests/conformance/overloading/tuple_option.verse),
[tuple/array](../../tests/conformance/overloading/tuple_array.verse),
[flattened distinct types](../../tests/conformance/overloading/tuple_flat_disjoint.verse),
[function/array](../../tests/conformance/overloading/function_array.verse),
[function/map](../../tests/conformance/overloading/function_map.verse) and
[overloaded tuple production](../../tests/conformance/overloading/overloaded_tuple_unpack.verse).
Their current expectations are ordinary positive/refusal oracles, not known
gaps. [Actual tuple/container calls](../../tests/verse/overload_shapes_tuples.verse)
and [receiver/argument/default/rollback traces](../../tests/verse/overload_shapes_order_rollback.verse)
exercise accepted execution. [Flattened dispatch](../../tests/verse/overload_shapes_flattened_dispatch.verse)
also covers inherited generic interfaces, named defaults and generic constructors. The [generated model](../../scripts/models/overload_shapes.py)
checks each table example in both declaration orders through top-level, named,
generic, interface/inherited, qualified and constructor calls. A 468-program
period covers all combinations; nightly checks scale the range.

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
# The 79 current-behavior/oracle checks; also part of scripts/check.sh.
bash tests/scripts/test-overload-conformance.sh

# Also measure the two remaining deviations; write exact current observations.
bash tests/scripts/test-overload-conformance.sh --include-gaps --report /tmp/overloading.json

# Both orders, six contexts, opaque generic patterns and real call oracles.
bash scripts/fuzz-overload-shapes.sh 468 1
```

The audit command reports known deviations as `GAP`, never as passing
conformance tests. Matching an upstream expectation reports `RESOLVED` so a
future fix need not preserve the wrong behavior. An unexpected result,
unrelated diagnostic, missing/emitted bytecode at the wrong phase, or Lean/C
disagreement fails the audit. Known-gap reproducers live outside the ordinary
positive/negative golden suites; no golden asserts a wrong acceptance or
refusal as correctness. The JSON report preserves exact stdout/status/stderr
and explicitly records the absence of Epic engine runs.

## Call packing (#501)

The four original packing reproducers now run as positive oracles. The
[combined packing fixture](../../tests/verse/call_argument_packing.verse) covers
explicit empty/singleton/multiple/nested tuples, bare generic tuples and
expected arrays, generic array class joins, contextual values inferred from
a named argument, and calls through function values.
[Methods and constructors](../../tests/verse/call_argument_methods.verse),
[multi-value and recursive calls](../../tests/verse/call_argument_values.verse),
[rollback and named/default order](../../tests/verse/call_argument_order.verse),
and [spawn/cancellation](../../tests/verse/call_argument_spawn.verse) retain
receiver-first evaluation, each supplied field once, written named order,
and omitted defaults in declaration order. Existing tuple-variable plus
named-argument calls remain supported as an OpenVerse extension to the
pinned Book restriction.

Overload admission compares both direct and adapted domains. A single array
formal can collide with several scalar formals; a bare generic formal can
accept their argument tuple; singleton tuple/scalar and empty tuple/no-formal
overloads also collide. The same `tuple(int)` value can unpack for `int`,
wrap for `tuple(tuple(int))`, or convert to `[]int`, so these domains also
overlap. Nested direct/flattened overlap and the existing wide `void` domain
are included. These are declaration refusals, rather than
an arbitrary preference for an overload with matching written arity.

Packing applies at a function boundary, retaining nested tuple fields. A
single scalar is not packed into an array; zero-element arrays use an explicit
`array{}` value with an inferable element type. Zero-formal/array overloads
remain distinct; scalar/array overloads can overlap through a tuple input. The
generic-array extension combines the pinned array and parametric rules; it
is not a claim of measured behavior in a released Epic compiler.

The generated `test-call-packing.sh` gate varies numeric values across six
shapes and ten caller contexts, comparing packed/explicit controls with exact
independent numeric and evaluation-trace oracles in Lean and C. Its recursive
context uses bounded tuple ranges for all six seed slots.

The open class family `tuple(t)` versus `[logic]t` also overlaps after
singleton packing even with `t:comparable`: `void` is comparable, and the
[same map value](../../tests/verse/call_argument_void_witness.verse) fits both
formals at `t=void`. The [open family is refused](../../tests/errors/call_pack_open_class_overlap.verse),
while a [fixed int specialization](../../tests/verse/call_argument_fixed_class.verse)
remains admitted. This finite erasure witness rules out using an occurs check
to claim that the open signatures are disjoint. The domain model retains
positive contexts with an additional positional hint or a named argument;
the class generator adds a required option name only when multi-positional
siblings would collide under the retained conservative tuple/option rule.
