# Rules of the remaining causes

The rules openverse takes from the Book of Verse for the causes the [map of
the remaining causes](book-test-conformance.md#the-remaining-causes-a-map)
lists, each pinned with the Book's words, its prose and its tests, at the
revision the other notes pin
([`beaa719`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0)).
Each section says what openverse did before, what it does now, and where
the rule lives. Where the prose and the tests disagree, openverse follows
the tests, and the section quotes both. No Epic compiler was run and no Epic
source code was read.

## A named parameter's default

**The rule.** A named parameter's default (`?X:t = e`) is its function's:
it has only the heap effects the function's own effects allow, and it
neither fails nor suspends, also of a `<decides>` or of a `<suspends>`
function.

**The Book.** The prose says where a default is evaluated, not what it may
do: "Verse evaluates default values in the function's defining scope; they
can reference: Module-level definitions, Class or interface members,
Earlier parameters" (ch. 6, `06_functions.md:105-109`). The tests settle
it, in `Tests/DefaultNamed.versetest`, sections `decides`, `suspends`,
`reads`, `writes`, `allocates` and `transacts` (lines 805-878):

- a default that fails, of a `<transacts><decides>` function, is refused
  (3512): `F<public>(?Value:int=DecideAndGetDefaultValue[option{1}])<transacts><decides>:int=Value`
  (`:820`, and `:824` with `[false]`);
- a default that suspends, of a `<suspends>` function, is refused (3512):
  `F<public>(?Value:int = SuspendAndGetDefaultValue())<suspends>:void={}`
  (`:844`);
- a default that constructs a `class<reads>` is valid in a `<transacts>` or
  `<reads>` function (`:850`, `:851`) and refused in a `<writes>`,
  `<allocates>` or `<computes>` one (`:852-854`); and so for `<writes>`,
  `<allocates>` and `<transacts>` classes (`:857-878`): the default's
  effects must be among the function's.

**openverse before.** A default was elaborated at each call that omits it,
in the caller's context: its effects were the caller's, it could fail in a
`<decides>` function and suspend in a `<suspends>` caller, and a failing
default was refused only at a call of a function that is not `<decides>`.
An uncalled function's default was never checked.

**openverse now.** Each default is elaborated once more, at its function's
definition (`checkParamDefaults`, `Elab/Functions.lean`, called from
`elabFn`): in the function's scope (the parameters before it, `Self` and
its fields in a method, type parameters opaque), with no failure context
and no suspension, its heap effects checked as the body's are (`fxCheck`).
The code of this trial is dropped; a call still evaluates the default as
before, so no program's code changes. A default that cannot be elaborated
in the function's scope (one that needs a call's type arguments, or that is
refused at the call for another reason) is left to its calls. The option
`--extended-defaults`, which keeps openverse's computed field defaults
(#511), keeps the reading of before as well; openverse's tests of that
reading (the waiting, dispatched and spawned defaults of #283) select it.

## An interface named twice

**The rule.** A class or an interface names each of its parents once: an
interface may be inherited again through another parent, but not twice
directly.

**The Book.** The prose is silent. The tests: "It's ok to inherit the same
interface more than once, but not directly. This restriction can be
removed." (`Tests/Interface.versetest:31-32`), then
`T2 := interface(T1, T1) {}` refused (3592, `:33`), "But indirectly is
allowed ..." (`:34`), and `C0 := class(T1, T1) {}` (`:40`); "Test that
redundant inheritance of a interface produces an error." (`:91`,
`C := class(T, T) {}`); `InterfaceDiamond.versetest:72-75`: "Currently
fail, but can be implemented. However, it's most likely an error in the
verse code."

**openverse before.** Accepted: a parent named twice was inherited once.

**openverse now.** `classHierarchy` (`Elab/Classes.lean`) refuses a parent
named twice with the same type arguments.

## `<override>` in an interface: left

The tests refuse it: "Interfaces can not override anything"
(`Tests/Interface.versetest:193`, a method `f<override>` and a field
`var v<override>` of an interface below another, 3523), "Can't override in
an interface" (`InterfaceWithFields.versetest:312`), and
`InterfaceDiamond.versetest:89`; the prose is silent. openverse gives an
interface's default a new body or value in an interface below it (#53's
interface defaults). The rule is one check (`EffectPolicy.checkPlaces`),
but measured it refuses 32 of openverse's tests of that feature
(`iface_default_copies*`, `multi_method_*interface*`, `inheritance`,
`qualified_slots`, …) and 45 generated programs (`classes` 4, `gadt_open`
20, `generic-mv` 21): an owner decision whether to retire the feature for
the Book's 3 cases, so it is left.

## A loop's body and a field's default are no failure contexts

**The rules.** A `loop`'s body is no failure context, also in a
`<decides>` function: an expression in it that can fail must be inside a
failure context of its own (an `if`'s condition, `option{…}`, …). A
field's default is no failure context either.

**The Book.** The tests: "`decides` is not allowed in `loop`."
(`Tests/Bugs/SOL-4199-BreakFromIf.versetest:79`, `Main()<decides>:void =`
then `loop: true?; break`, 3512); "Failable inside loop is disallowed."
(`SOL-1987-IfDoesNotDetectNestedConditional.versetest:22`, a loop in an
`if`'s condition); `FlowControl/Case.versetest:291` (a `case` with no `_`
in a loop of a `<transacts><decides>` function, 3512). For fields:
"Test that effects aren't allowed in class member default initializers or
do clauses unless declared on the class." (`Effects.versetest:536`), then
`c:=class{X:int=option{0}?}` refused (3512, `:537`); the prose: "Class
member initializers and block clauses are implicitly restricted to have no
more effects than what the class declares" (ch. 13, `13_effects.md:830`),
and a class declares no `<decides>` (openverse refuses one, #508).

**Where the Book disagrees with itself.** Ch. 8 says "Functions marked with
`<decides>` create a failure context for their entire body"
(`08_failure.md:122`); its tests take a loop's body out of it. openverse
follows the tests.

**openverse before.** A loop's body inherited the failure context around
it, so a failure in a `<decides>` function's loop failed the function; a
field's default could fail, and a construction that took it failed.

**openverse now.** The loop's body is elaborated with no failure context
(`.loop`, `Elab/ExpressionControl.lean`; the refusal says why,
`Elab/Statement.lean`). A field's default that can fail is refused where
each default is checked once (`elabFieldDefaults`, `Elab/Functions.lean`);
`--extended-defaults` keeps openverse's failing defaults, as it keeps its
other computed field defaults (#511).

## A filter that is a literal

**The rule.** Each filter of a `for`, a clause that is no binding, must be
able to fail.

**The Book.** Ch. 7: "Each filter must be failable, and if any fails, that
iteration is skipped" (`07_control.md:657`); "Filters must be failable:
Filter conditions must contain at least one expression that can fail."
(`:836-837`); the tests: `NoFailure:[]int= for(X:=1 .. 4; 1) { X }`
refused, "Filter can not fail" (`FlowControl/for.versetest:223`, 3513).

**openverse now.** A filter that is a literal is refused with the source
rules (`checkForClauses`, `Elab/Source.lean`), beside the `for` of literal
clauses only. **Left:** the whole rule. Checked on every filter's
elaborated code, it refuses 153 of openverse's tests and 826 generated
programs (the `choice`, `context`, `fields`, `heterogeneous`, `mv-*` and
`gadt_*` families), which write `Print(…)`, `set X += 1` or a choice that
cannot fail as clauses of a `for`: an owner decision whether to refuse them
all now.

**Also in ch. 7.** "Cannot define mutable variables: Using `var` to declare
variables in the for clause is not allowed" (`07_control.md:842-843`),
where the tests accept `for(X:=1 .. 2, var Temp:rational = 10/X) { X }`
(`FlowControl/for.versetest:235-236`, `assert_valid`): openverse follows
the tests and accepts it.

## A module constant has no side effect

**The rule.** The value of a module's constant writes nothing: its
initializer, and what it calls or constructs, has no `<writes>` effect. A
function with no heap specifier is `<transacts>`, and so is a class or a
struct with none, so a constant cannot call such a function or construct
such a class; `<computes>`, `<reads>` and `<allocates>` ones it can.

**The Book.** The tests: "Test that all non-local variables initializers
(module, instance) can't have side effects."
(`Tests/Features/DefaultValueAssignment.versetest:199`), then a constant
whose value calls a function that sets a field, directly (`:200`) or
through another (`:215`, `:225`, in a module), refused (3582); "Test that
calling methods (which may have side-effects) produces an error"
(`Modules/ModuleDefinitions.versetest:278-279`: `j:int=hasSideEffect()`,
3582); "Ensure constructor effects of prototype is copied to each
instance" (`ParametricTypes.versetest:459-468`): a `class<computes>`
constructed by a module constant is valid, a `class<transacts>` one refused
(3512). The prose: "Instances of `<unique>` classes with `<allocates>` can
be created at module scope, as long as their construction does not actually
allocate mutable memory" (ch. 16, `16_modules.md:617`); every module-scope
instance of the tests is of a `<computes>` class
(`Modules/ModuleScopedInstances.versetest:12-35`). Whether a construction
"actually" allocates mutable memory is the VerseVM's link-time check (9003,
`GlobalVariables.versetest` 86-105, `verse_vm_only`), which openverse does
not make.

**openverse before.** A constant's heap effects were inferred from its
initializer and allowed, whatever they were (a constant is computed at each
use, so it could not hold a mutable object, but it could write).

**openverse now.** `elabFunctions` (`Elab/Functions.lean`) refuses a
constant whose initializer has the effect `<writes>`, saying what has it.
`<reads>` is left allowed, as the tests pin only writes.

## A loop that nothing leaves

**The rule.** A `loop` of a function that cannot suspend has a way out: a
`break` of its own, or a `return`.

**The Book.** The tests: "Ensure loop is not empty" (`loop {}`) and "Ensure
loop has matching break and don't confuse with non-matching nested break"
(`Tests/FlowControl/Break.versetest` 117-120, 160-171, 3579); a `<suspends>`
function's loop with no `break` is valid ("Allow loop with at least one
async expression", `:17-29`). The prose: the loop "continues until
explicitly broken" (ch. 7, `07_control.md:463`).

**openverse before.** Accepted; such a loop ran until the program's fuel
was spent, or a runtime error.

**openverse now.** `checkLoopExits` (`Elab/Source.lean`), with the source
rules. Programs: `tests/verse/overflow.verse`, whose loop ended at an
overflow, gains a `break` that is never taken.

## `race` arms, `(super:)` and `spawn`'s effects: left

Three more rules of the accepted refusals are one check each, measured and
left, as each retires a reading openverse's own tests are about:

- **Every arm of `race` and `rush` can suspend** ("Ensure all top-level
  expressions in race/rush are async", `Coroutines/Concurrency.versetest:831`,
  3538; the prose is silent): 9 tests (`task_cancel_rush_loser`,
  `sync_race`, `fn_values_method_variance_async*`, …) race an immediate arm
  on purpose, and an arm that calls a suspending function value is not yet
  known to suspend where `sync`'s rule looks (1 case).
- **`(super:)M` only in an override of `M`** (`Super.versetest` 183, 238,
  3612): 27 tests call `(super:)` for another method or in a block
  (`multi_method_cross_super_*`, `choice_super_*`,
  `class_cast_refine_super*`, …), and 20 generated programs (2 cases).
- **`spawn` has `<transacts>`'s heap effects** ("spawn requires the
  transacts effect…", `Effects.versetest:554`; in a `<computes>` function,
  3512 on both VMs, `:558`, `:573`): 12 tests spawn from narrower
  functions (`spawn_narrow_callers_*`, `choice_refined_spawn_narrow`), and
  20 generated programs (2 cases).
