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
