# Type aliases

The rules openverse takes for type aliases, `name := t` and the parametric
`name(u:type, …) := t`, the readings it had to choose, and what it does not
do. [LANGUAGE.md](../LANGUAGE.md#type-aliases) states the rules for users;
[DESIGN.md](../DESIGN.md#type-aliases-a-substitution-before-elaboration)
says how they are built.

## Sources

- The [Book of Verse at `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs):
  chapter 11, "Type Aliases" (`docs/11_types.md` lines 1280-1397) and
  "Metatypes" (lines 1454-1459); chapter 10, "Disallowed: Direct Type Alias
  Recursion" (`docs/10_classes_interfaces.md` lines 1529-1556) and
  "Aliases" (lines 1880-1927); chapter 16's module example (`docs/16_modules.md`
  lines 214-215); chapter 18, "Module and Type Aliases" (`docs/18_evolution.md`
  lines 240-245); chapter 2 on `string` (`docs/02_primitives.md` line 603).
- The same snapshot's tests: [`Tests/TypeAlias.versetest`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/TypeAlias.versetest)
  and [`Tests/ParametricTypes.versetest`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/Tests/ParametricTypes.versetest)
  (lines 18-23, 250-254, 274-276, 292-294, 303-322 and 589), cited by
  line.
- Retrieved 2026-11-13. No Epic source was read and no Epic engine was run.

**Release status.** None of these sections carries an "Unreleased Feature"
marker. The Book documents the head of Verse's development branch, so this is
development-branch evidence; no released UEFN version is verified.

## Quotations

- Ch. 11, lines 1282-1287: "Type aliases allow you to create alternative
  names for types, making complex type signatures more readable and
  maintainable. They're particularly valuable for function types, parametric
  types, and frequently-used type combinations. A type alias is created using
  simple assignment syntax at module scope". The example (lines 1292-1304):
  `coordinate := tuple(float, float, float)`, `entity_map := [string]entity`,
  `player_id := int`, `update_handler := type{_(:float):void}`,
  `validator := int -> logic`, then `Origin:coordinate = (0.0, 0.0, 0.0)`.
- Lines 1307-1312: "Type aliases are compile-time only - they create no
  runtime overhead and are purely for programmer convenience and code
  clarity. A type alias is an alternative name, not a new type. Aliases do
  not create distinct types the way `newtype` does in some languages. Values
  of the alias and the original type are completely interchangeable". The
  example passes a `game_id` where a `player_id` is expected (lines 1317-1330).
- Lines 1333-1358: "Type aliases can have access specifiers that control
  their visibility across modules" (`PublicAlias<public> := int`,
  `InternalAlias<internal> := string`); "Only `<public>` and `<internal>`
  are available here. Writing `ProtectedAlias<protected> := float` at module
  scope is an error, because `protected` and `private` are meaningful only
  inside a class or an interface."
- Line 1360: "A type alias cannot be more public than the type it aliases"
  (`PublicToInternal<public> := internal_class` in a module, error 3593).
- Lines 1389-1397, "Requirements": "Type aliases can only be defined at
  module scope. They cannot be defined inside classes, functions, or any
  nested scope." "Type aliases must be defined before they are used. Forward
  references are not allowed." "Type aliases are not first-class values and
  cannot be used as such."
- Lines 1454-1459: "Collection and function types have to be named by an
  alias first" (to write `subtype([]int)`, a metatype openverse does not
  have).
- Ch. 10, lines 1531-1532 and 1540-1555: "You cannot define a parametric
  type that directly aliases to a structural type containing itself":
  `t(u:type) := []t(u)`, `[int]t(u)`, `?t(u)`, `u->t(u)`, `t(u)->u`, "These
  fail because they create infinite type expansion"; "The way round this is
  to wrap the recursive reference in a class."
- Lines 1882-1927: "You can create type aliases that simplify complex
  parametric type expressions": `string_map(t:type) := [string]t`,
  `optional_array(t:type) := []?t`; "Aliases are not restricted to named
  types. Function types and tuple types can be given names in exactly the
  same way": `transformer(input:type, output:type) := input -> output`,
  `pair(t:type, u:type) := tuple(t, u)`, used as
  `T:transformer(int, string)`.
- Ch. 16, line 214-215: in a module, `coordinate<public> := tuple(float,
  float)` beside data that states its type.
- Ch. 18, lines 242-245: aliases "can be added" and "removed" without
  changing a persistable type; "Type aliases must reference the same type."
- Ch. 2, line 603: "Verse provides the type alias `string` for `[]char`".

The tests add:

- `TypeAlias.versetest` line 10: `T1:subtype(C0)= C0 # this is accepted,
  but is not a type alias: it's instead a class-typed data definition.`
- Lines 14-89: aliases of `type{_():int}`, `?int`, `?O0` (an alias of an
  alias), `[]int`, `subtype(C0)`, `[string]int` and `int -> int`, used in
  parameter types. Lines 41-42: `O0:=?O1; O1:=?int` and `O0:=?O1; O1:=?O0`
  are errors.
- Lines 100-109: `C := class {O := ?int}` and `f():void = {O := ?int}`
  ("type aliases may only occur at module scope"), `t{}` ("used as macros",
  3545) and `t[X]` ("used as functions", 3552) on `t:=?int` are errors.
- Lines 161-193: `a<public> := c` before `c<public> := class{…}`, then
  `d := class(b)` with `b := c`, `AliasesOfClasses.a{}.Foo()`,
  `d{}.(AliasesOfClasses.a:)Foo()`; `f<public> := e` of an enum, with
  `AliasesOfEnumerations.f.E0` equal to `…e.E0`; `t := int` inside a module.
- Lines 199-225: nine pairs, `a := int; b := a` (and `a -> logic`, `?a`,
  `tuple(a,logic)`, `[]a`, `[a]logic`, `type{_(:a):logic}`, `a(b)` of a
  parametric class, a class field `X:a`) valid, and each with `b` before
  `a` an error (3502).
- Lines 227-239: a `<public>` alias of an internal class, enum, struct or
  interface, or of a compound of one (`?c`, `[]c`, `tuple(int, c)`,
  `int->c`, …), is an error (3593).
- `ParametricTypes.versetest` lines 18-23: `t(u:type):=tuple(u,u)`,
  `u->u`, `[]u`, `[int]u` valid; lines 250-254 and 274-276: recursive
  parametric aliases are errors, also when used; lines 303-322: aliases of
  aliases, `t1(u:type) := []t0(u)`; line 589: `list(t:type) := ?cons(t)`
  with `cons` a class, recursion through the class.

## The rules openverse takes

1. **What may be named.** Any type: the Book's and the tests' examples
   cover the built-in types, `?t`, `[]t`, `[k]v`, `tuple(…)`, function
   types in both spellings, classes, enums, other aliases and parametric
   types applied to types. openverse takes every type it can write, so
   also structs, interfaces and refinement types. `subtype(…)` is not a type
   openverse has (types as values), so an alias of it is refused as an
   unknown type.
2. **A type or a value.** The Book writes an alias as "simple assignment
   syntax", the same as a constant's `X := e`, and its tests say a
   definition with a written type (`T1:subtype(C0)= C0`) is no alias. The
   reading: `name := e` at the top level or in a module is an alias when
   `e` is a type, that is, written as only a type can be (`?int`, `[]t`,
   `int->int`, `tuple(…)`, `type{_(…):r}`), or a type's name, or a
   parametric type's name applied to as many types as it has parameters;
   else it is a constant. Before aliases, a type's name was no value (`X :=
   c` with `c` a class was refused as "unknown identifier 'c'"), and
   `X := c(Y)` with `Y` a constant, a cast, and `X := any(Y)` remain
   constants, so the rule changes the meaning of no program that compiled.
   `name(u:type, …) := t` is always a type.
3. **Where.** Module scope only: the top level or a module, never a class
   or a function (lines 1389-1390, tests 100-103). openverse parses an
   alias only as a top-level or module definition; `O := ?int` in a class
   or a function body stays a parse error.
4. **The same type.** "An alternative name, not a new type ... completely
   interchangeable." openverse writes each alias out before elaboration, so
   an alias is the type it names in assignments, calls, overload
   distinctness (`F(:player_id)` and `F(:int)` cannot both be defined, as
   the Book's `F(:int)` and `F(:comparable)` overloads are judged by their
   types), casts and comparisons. *Reading:* the Book does not say what
   messages show; openverse shows the type the alias names.
5. **Parametric aliases.** A function from types to types: `t(u:type) := e`
   applied as `t(int)` is `e` with `int` for `u`, with as many type
   arguments as parameters. *Reading:* each parameter is `u:type`; a bound
   (`u:subtype(comparable)`) is refused as not supported, since nothing
   after the substitution would check it (the Book's one example of a
   bounded alias is in a commented-out crash test, `TypeAlias.versetest`
   line 157).
6. **Recursion.** An alias that names itself, directly or through other
   aliases, is an error (ch. 10, tests 41-42, 250-254, 274-276); recursion
   through a class (`list(t:type) := ?cons(t)` with `cons` holding a
   `?cons(t)`) is fine, as the class is a type of its own.
7. **Defined before used.** "Forward references are not allowed" (line
   1394, tests 199-225): an alias may be used, in a type or as a value, only
   by a definition after it, also another alias (so a cycle of aliases is
   always caught, at its first forward use). An alias may name a class
   defined after it (test 162). *Reading:* "after" is in the order openverse
   loads definitions: within a file as written, an imported file's before
   the importing file's, a directory's files in sorted order.
8. **Not values.** "Not first-class values" (line 1397; tests 105-109).
   *Reading* from tests 161-193: an alias of a class, interface, struct,
   enum or refinement type stands for it where a value, a construction, a
   parent, a qualifier or an enum's value names that type (`a{}`,
   `class(b)`, `(a:)Foo()`, `f.E0`, `a[X]`); any other alias in those
   places is an error. A parametric alias constructs as `box_of(int){…}`.
9. **Names.** Verse has no shadowing: no definition at any scope takes an
   alias's name, and an alias takes no built-in type's name.
10. **Modules.** An alias in a module is a member like any other, used
    from outside as `M.point` when `<public>`. Chapter 16's rule that module
    data states its type does not apply to it (line 215 writes one beside
    such data).
11. **Access.** `<public>` and `<internal>` mean what they mean for other
    module members. *Not enforced:* `<protected>`/`<private>` on an alias
    (lines 1355-1358) and a `<public>` alias of an internal type (line
    1360, tests 227-239) are accepted, as openverse accepts access
    specifiers without enforcing them (LANGUAGE.md's Readings): the Book
    refuses those with the same errors as public functions whose
    signatures name internal types, one general rule that is an owner's
    decision ([book-test-conformance.md](book-test-conformance.md), "access
    specifiers"). The 12 Book cases are listed there.
12. **Checks.** The names in an alias's type are checked where it is
    defined (an unknown name is an error even when the alias is unused);
    the rest of its type's checks (a map key that must be comparable, a
    parametric type's arguments) where it is used, as if written there.
    An unused `a := [c]int` with `c` a class that is not comparable is
    therefore accepted.

## What is not supported

- Bounded parameters of a parametric alias (rule 5).
- Aliases of metatypes, `subtype(…)` and `castable_subtype(…)`.
- A function type written with a name in place of `_`,
  `type{F(:u):u}` (`ParametricTypes.versetest` line 19), which openverse's
  parser does not read anywhere.
- Qualified definitions such as `(AliasesOfClasses:)e<public> := …`
  (`TypeAlias.versetest` line 166): qualified names are a cause of their
  own in the survey, and they keep 12 of its alias cases refused.
