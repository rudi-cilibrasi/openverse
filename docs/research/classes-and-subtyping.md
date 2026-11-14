# Classes and subtyping: the Book's rules

The rules behind the causes about classes and subtyping of the Book test
survey ([book-test-conformance.md](book-test-conformance.md), "Classes and
subtyping: the map"), pinned with the Book's words, one section per form
built. The Book is the pinned revision `beaa719b`; chapter lines are of its
`docs/`, test lines of its `Tests/`. Where the prose and the tests
disagree, openverse follows the tests, and the section quotes both.

## Recursive parametric types

**The rule.** A parametric class or interface may name itself in the types
of its fields only at its own type parameters, in their order, and no
parametric class or interface may name another one in its fields that
names it back, directly or through others.

- Ch. 10, "Recursive Parametric Types" (`10_classes_interfaces.md:1494-1497`):
  "Parametric classes can reference themselves in their field types, …
  The key requirement is that the self-reference uses **the same type
  parameter** — this is the only form of recursion Verse allows."
- "Disallowed: Polymorphic Recursion" (`:1578-1581`): "Polymorphic
  recursion occurs when a parametric type references itself with a
  **different type argument**", with `Next:my_type(?t)` and
  `Next:?bi_list(u, t)` ("parameters swapped") as its errors.
- "Disallowed: Mutual Recursion" (`:1609-1612`): "Mutual recursion between
  multiple parametric types is not supported either; each of the two
  definitions below is rejected on its own".
- The tests: `ParametricTypes.versetest` 262-271, "Polymorphic recursion is
  not yet supported", "Mutual recursion is not yet supported", 3509 each.

The prose and the tests agree. The rule is about field types (the
chapter's words and every example); a method's signature is not looked
at. Classes without type parameters may name each other (ch. 10's linked
structures). The types the front end writes (named with `$`: closures,
type values) are not looked at.

**In openverse.** `checkParametricRecursion` (`Elab/Classes.lean`), with
the class hierarchy (phase 4), after the inheritance cycles: each
parametric class's own fields, those with accessors too, are walked for
applications of parametric classes and interfaces (`STy.applicationsOf`,
over `STy.children`); one of itself at other arguments is refused, then a
cycle among the others.

```verse
my_type(t:type) := class:
    Value:t
    Next:?my_type(?t) = false
```

`field 'Next' of my_type names my_type(?t), my_type at other type
arguments than its own: a parametric type refers to itself only as
my_type(t) (Book of Verse ch. 10, "Disallowed: Polymorphic Recursion")`;
and for `t1(t)`'s `Next:?t2(t)` with `t2(t)`'s `Next:?t1(t)`: `the fields
of t1 name t2, and those of t2 name t1: parametric types cannot be
mutually recursive (Book of Verse ch. 10, "Disallowed: Mutual
Recursion")`.

**What changed.** An interface with `Next:n([]t)` was refused when a
variable of its type needed a placeholder (#157); it is refused where it
is defined now (`tests/errors/iface_placeholder_grows.verse`, renamed
`parametric_recursion_interface.verse`). `tests/errors/class_param_const_mutable.verse`
named `w(cell(int))` inside `w(t)` to reach an object with a `var` field;
it reaches it through a `holder(cell(int))` now, with the same message.

## Final super classes

**The rules.**

1. `<final_super>` goes on a class (built before, `EffectPolicy.specifierPlaces`),
   which has a parent, a class or an interface.
2. A class right below a `<final_super_base>` class or interface is
   `<final_super>` (built before); an interface below one need not be.
3. `GetCastableFinalSuperClass[B, X]`, with `X` of the type `B`, gives the
   class `C` that is `<final_super>`, castable, has `B` among its parents,
   and is `X`'s class or above it, as a value of `castable_subtype(B)`; it
   fails when there is none. Of the classes that list an interface `B`, the
   topmost ("least specific"); a class `B` is the parent of one class at
   most on any chain.
4. `GetCastableFinalSuperClassFromType[B, T]` does the same for the class
   the type `T` holds; `T` may be any type, and one not below `B` makes it
   fail.
5. A `B` that is no class or interface (`int`, `float`, `any`) makes both
   fail. Both are `<reads><decides>`.

**The Book.**

- Ch. 10, "Final" (`10_classes_interfaces.md:2904-2909`): "The related
  `<final_super>` specifier does **not** prevent further subclassing.
  Instead, it guarantees that all subclasses of this class will always
  directly inherit from it"; `:2927-2931`: "`<final_super_base>` marks the
  root of a restricted inheritance tree. Its purpose is to work with
  `GetCastableFinalSuperClass`, which finds the `<final_super>` class in the
  hierarchy for a given instance."
- Ch. 11, "GetCastableFinalSuperClass" (`11_types.md:1721-1726`): "Both
  return a `castable_subtype` representing the least specific
  `<final_super>` class that: 1. Directly inherits from the specified base
  type 2. Is in the inheritance chain of the instance/type. The function
  fails if no appropriate `<final_super>` class exists." `:1806-1809`: "It
  fails when no `<final_super>` class exists between base and instance,
  when the queried type is itself the instance type, so that there is no
  level to walk up from, or when the instance is not a subtype of the
  base."
- The API reference (`docs/api/verse_runtime_api.html`, module
  `/Verse.org/Verse`, `CastableFinalSuperClass`):
  `GetCastableFinalSuperClass<epic_internal><native>(base_type:type,
  Instance:base_type)<reads><decides>:castable_subtype(base_type)`, "Return
  an immediate subclass of base_type that is <castable> and <final_super>
  and is also shared with Instance. Otherwise failure."; and
  `GetCastableFinalSuperClassFromType<epic_internal><native>(base_type:type,
  sub_type:subtype(base_type))<reads><decides>:castable_subtype(base_type)`,
  the same "shared with sub_type".
- The tests: `Attributes/FinalSuperAttribute.versetest` (49-51, "final_super
  types must have some sort of base type", 3679; 36-48, 3680; 27-29, an
  interface below a `<final_super_base>` one); `GetCastableFinalSuperClass.versetest`
  (every case `verse_vm_todo`: "GetCastableFinalSuperClass is not defined
  in the new VM because of gaps in VNI support for types", line 29; the
  survey takes the BPVM's expectations): the queries of 32-99 and 147-338;
  the instance of the base type, 101-125 (3509); the result a
  `castable_subtype` of the first argument, 127-145 and 182-202 (3509);
  not castable, 332, 337; types that are no classes, 296-304.

**Where the Book disagrees with itself.** The API reference types the
second parameter of `GetCastableFinalSuperClassFromType` as
`sub_type:subtype(base_type)`, so a type not below the base would be
refused. The tests pass such types and expect the call to compile and
fail: `GetCastableFinalSuperClass.versetest:109`, `assert
{not GetCastableFinalSuperClassFromType[a_class, base_type] }` (`base_type`
is above `a_class`); `:303-304`, `[base_type, int]`, `[base_type, any]`;
`:330-331`, `[base_type, ix3_interface]`, `[i_base0, i_base1]`. openverse
follows the tests: the second argument is any type, and ch. 11's "fails …
when the instance is not a subtype of the base" is then the run-time
failure. The instance variant's `Instance:base_type` agrees with its tests
(101-125 refuse an instance of another type).

The `<epic_internal>` access of both is not modelled: the Book's tests
call them from ordinary code.

**In openverse.** The specifier rule is in `classHierarchy`
(`Elab/Classes.lean`); the functions are a source pass, `FinalSuper.desugar`
(`Front/FinalSuper.lean`), run before types as values are written
(`TypeValues.desugar`). A call becomes a call of a helper per function and
`B`:

```verse
$GetCastableFinalSuperClass:B(X:B)<reads><decides>:castable_subtype(B) =
    if (C1[X]) then C1 else if (C2[X]) then C2 else (fail)
$GetCastableFinalSuperClassFromType:B(T:type)<reads><decides>:castable_subtype(B) =
    if (subtype(C1)[T]) then C1 else … else (fail)
```

with the candidates topmost first: the classes that are `<final_super>`,
castable, list `B` among their parents and that some object can have (one
at or below them is neither an interface nor abstract; a cast to a class no
object has is refused as one that always fails, and it would fail). A cast
of a type value to `subtype(C)` succeeds when it holds `C` or a class or
interface below `C`. `TypeValues` then writes the classes named as values
and `castable_subtype(B)` as for any program, so the result is below
`castable_subtype(B)` through the interfaces of the classes between. For a
`B` that is no class or interface the helper's body fails, and its result
type is `type`. For this, type values became `<computes>` (making one and
casting through one has no effect; the commit before), and `any` and
`comparable` values of `type` (`X:type = any`; `subtype(any)` is still not
written). A program that defines a function of either name calls its own.

`B` must be a type's name written at the call: a type parameter or a value
there is refused ("GetCastableFinalSuperClass's first argument is a type
written there, the base type, and B is no type openverse knows there"), and
so is an applied parametric type (no `<castable>` class has a parametric
parent in the tests; it would need the candidates at type arguments).

```verse
component := class<castable>{}
physics := class<final_super>(component){}
rigid := class(physics){}
```

`GetCastableFinalSuperClass[component, rigid{}]` gives `physics`;
`GetCastableFinalSuperClass[physics, rigid{}]` fails (`rigid` is not
`<final_super>`); `GetCastableFinalSuperClassFromType[component, rigid]`
gives `physics`. `tests/verse/final_super.verse` runs the cases, in Lean
and C; the refusals are `tests/errors/final_super_*.verse`.

## `<computes>` with the additive heap effects

**The rule.** Of the heap specifiers, `<computes>` and `<transacts>` are
exclusive (with `<converges>`, at most one of them), and `<reads>`,
`<writes>` and `<allocates>` additive: `<computes>` with additive ones
allows those (`<computes><allocates>` allows allocating), on a function, a
function type, a class, an interface or a struct; `<computes>` alone allows
none; no heap specifier, or `<transacts>`, all three.

- Ch. 13 (`13_effects.md:99-105`): "Effect specifiers can be further
  divided into *exclusive* specifiers (`<converges>`, `<computes>`,
  `<transacts>`) and *additive* specifiers (`<suspends>`, `<decides>`,
  `<reads>`, `<writes>`, `<allocates>`). A function may have at most one
  exclusive specifier but can combine multiple additive ones. For example,
  `<computes><decides>` is valid (pure computation that may fail), but
  `<computes><transacts>` is an error (cannot have two exclusive
  effects)." The table (`:111-116`): `<reads>` `{reads}`, `<writes>`
  `{writes}`, `<allocates>` `{allocates}`, `<transacts>` `{reads, writes,
  allocates}`, `<computes>` `{}`.
- The tests: `Attributes/allocates.versetest:4-5`, "<allocates> only works
  with classes, interfaces, structs, & functions. Combines with <varies> and
  <computes>, but redundant with <transacts>", and its cases 6-32 (valid
  with `<computes>` on a class, an interface, a struct and a method), 57
  (a `var` field in a `<computes><allocates>` class), 59 (3512, the same in
  a `<computes>` class); `Attributes/unique.versetest:86-137`, "Allocating
  a <unique> class requires <allocates>. So <unique> classes can be created
  in <transacts> without further annotation, but <varies> and <computes>
  require an explicit <allocates>"; the key classes of `Map.versetest`,
  `Operators/CompareMap.versetest` and `weak_map.versetest`
  (`class<unique><allocates><computes>`).

The prose and the tests agree.

**In openverse.** It refused `<computes>` with any heap specifier ("<computes>
excludes the heap effects … that F also has"), in `EffectPolicy.checkSpecs`
(classes, interfaces, structs, function types) and `checkExclusive`
(`Elab/Signatures.lean`, functions). Those refusals are gone; the
exclusive rule stays ("has more than one of <converges>, <computes> and
<transacts>"). A function's allowed effects (`allowedFx`) already read the
named ones first; a data type's construction budget (`EffectPolicy.constructionFx`)
does too now. A function with several values computed at its calls (#283)
must be effect-free: `<computes>` with no additive heap specifier
(`Choice.lean`).

**What changed.** `tests/errors/fx_computes_and_reads.verse` and
`tests/errors/fx_generic_computes.verse` expected the old refusal of
`<computes><reads>`; they now test that such a function may not write
("F sets a var field, which its effects (<reads>) do not allow").

## A field re-declared with `<override>` and no value

**The rule.** `F<override>:t` with no value re-declares an inherited field
`F` (at the same type; at a subtype, below) with no default: a construction
of the class, or of one below it that gives no default, gives `F`. It
needs no new default.

- Ch. 10, "Overriding Members" (`10_classes_interfaces.md:3172-3175`):
  "Field overrides can provide different default values or specialize to
  subtypes": a new default is one thing an override can do, not what it is
  for.
- Ch. 10, "Concrete" (`:2112-2114`): "Re-declaring the member with
  `<override>` does not satisfy the requirement — it still needs an
  initializer", with `thing := class<concrete>(has_field) { Field<override>:int }`
  an error (3519).
- The tests: `Attributes/override.versetest:29-35` (`A<override>: int`
  with no value, constructed `c1{ A:= 4 }`), `:37-47` ("overriding data
  member with base specifying an initializer": `c3{}` is refused, 3600,
  "Object archetype must initialize data member": the inherited default
  is not kept), `concrete.versetest` 59, 110, 230, `SOL-3366:53`,
  `SOL-9745` (each concrete class that re-declares with no value is
  refused, 3519).

The prose and the tests agree. That the inherited default is dropped is
the tests' (`override.versetest:37-47`); the prose says nothing of it.
`concrete.versetest:110-114` re-declares a field of a `<concrete>` class
with no value in a subclass that is not marked, and is accepted ("is this
actually valid?"): with the tests' reading of `<concrete>` as inherited
(the owner's open question, [Concrete classes and their
subclasses](https://github.com/rudi-cilibrasi/openverse/wiki/Concrete-classes-and-their-subclasses)),
it would not be.

**In openverse.** `classFields` (`Elab/Classes.lean`) refused such a field
("F<override> must give a new default"); it now gives it no default. The
default two interfaces give a field is settled by any override of it, with
a value or none.
