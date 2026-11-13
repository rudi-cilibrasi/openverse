# Access specifiers

The rules openverse takes for access specifiers (`<public>`, `<internal>`,
`<protected>`, `<private>`, `<scoped{…}>`, `<epic_internal>`): what each
admits, its default for each kind of definition, where it may be written,
how overrides and `var` take it, and the consistency rules among
definitions; the error codes the Book's tests give; where the Book's prose
and its tests disagree; the readings openverse had to choose; and the
design. [LANGUAGE.md](../LANGUAGE.md#access) states the rules for users;
[DESIGN.md](../DESIGN.md#access-one-order-checked-where-names-are-resolved)
says how they are built.

Before this note openverse read access specifiers as a documented reading
(LANGUAGE.md, Readings, "Access specifiers other than `<public>`"): a module
member was `<public>` or internal, and every other specifier, a struct
field's, and a `<public>` definition naming an internal type were accepted
and not enforced. The [survey](book-test-conformance.md) counted 107 cases
the Book's tests refuse and openverse accepted, the largest group of
accepted refusals. The owner's rule is to follow the Book, so the reading is
retired.

## Sources

- The [Book of Verse at `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs):
  chapter 12, "Access Specifiers" (`docs/12_access.md` lines 1-595 and
  1250-1268); chapter 10, "Access Specifiers" (`docs/10_classes_interfaces.md`
  lines 2067-2091); chapter 9 (`docs/09_structs_enums.md` line 29); chapter 11,
  type aliases (`docs/11_types.md` lines 1333-1381); chapter 16, "Access Denied
  Errors" (`docs/16_modules.md` lines 1226-1251); chapter 6, nested functions
  (`docs/06_functions.md` lines 1176-1182); chapter 18, "Access Specifiers"
  (`docs/18_evolution.md` lines 198-202).
- The same snapshot's tests, cited by line: `Tests/ArchetypeAccessSpecifiers.versetest`,
  `Attributes/AccessLevelInheritance.versetest`, `Classes/AccessSpecifiers.versetest`,
  `Interfaces/AccessSpecifiers.versetest`, `InterfaceAccessVisibility.versetest`,
  `DigestVisibility.versetest`, `VarAccessSpecifiers.versetest`,
  `Attributes/scoped.versetest`, `Attributes/AccessSpecifiersDisallowedOnLocalVars.versetest`,
  `Attributes/intrinsic.versetest`, `Modules/AccessSpecifiers.versetest`,
  `Modules/Module.versetest`, `Modules/ModuleDefinitions.versetest`,
  `ParametricTypes.versetest`, `TypeAlias.versetest`, `NestedFunctions.versetest`,
  `Union.versetest` (1323-1370), and `Bugs/SOL-5564-PublicOverrideOfDefinitionInNonPublicScope.versetest`,
  `Bugs/SOL-7898-DisambiguateSuperTypesByAccess.versetest`,
  `Versions/v1/v1-PublicStructFields.versetest`,
  `Versions/FN36.00/FN36.00-DetectInaccessibleTypesInParametricTypeArguments.versetest`,
  `Versions/FN40.00/FN40.00-EnforceInterfaceDataMustBeInitializedOrAccessible.versetest`.
- Retrieved 2026-11-13. No Epic source was read and no Epic compiler was run;
  the tests' expectations are the oracle.

## Quotations

- Ch. 12, lines 3-4: "An access specifier controls where a definition can be
  referenced from. Verse has five levels, plus one reserved for Epic-authored
  code." The table, lines 10-17: `<public>` "Universally accessible";
  `<internal>` "Only within the module (default)"; `<private>` "Only in
  immediate enclosing scope", "Local to class/struct"; `<protected>`
  "Current class and subtypes"; `<scoped>` "Current scope and enclosing
  scopes"; `<epic_internal>` "Scopes with the /Verse.org, /UnrealEngine.com,
  and /Fortnite.com domains", "`<epic_internal>` is only usable by
  Epic-authored code".
- Ch. 12, lines 21-23: `<public>` makes "an identifier universally
  accessible from any code that can reference the containing module or
  type". Lines 58-63: "The public specifier can be applied to modules,
  classes, interfaces, structs, enums, methods, and data members."
- Ch. 12, lines 67-69: `<protected>` allows "access within the defining class
  and any classes that inherit from it". Lines 110-112: `<private>` limits
  "visibility to the immediately enclosing scope". Lines 151-154: `<internal>`,
  "the default access level when no specifier is provided, makes members
  accessible within the defining module but not outside it".
- Ch. 12, lines 195-196: "A scoped access level is created using the
  `scoped{...}` expression, which takes one or more module references";
  lines 217-221: it "can then be used as a specifier on classes, functions,
  variables, and other definitions. Code within any of the listed entities
  can access the scoped member". Lines 320-323: scoped access "does not make
  intermediate types or modules visible. To access a scoped member, you must
  be able to see the entire path to it". Lines 362-363: "A definition can
  only have one scoped access level". Lines 406-409: "A `<scoped>` grant
  applies only to the definition that carries it. The members of that
  definition keep their own accessibility". Lines 455-457: "reaching
  `A.B.C` from a granted scope needs the grant on `A`, on `B`, and on `C`".
- Ch. 12, lines 384-386: "When a class member has scoped access, overriding
  members in subclasses can maintain or narrow that access"; example 11,
  lines 398-399: `ComputeValue<override>():int = 100  # Now internal to this
  module` ("Can override with same or more restrictive access").
- Ch. 12, lines 543-549: "The syntax places the write-access specifier on the
  `var` keyword and the read-access specifier on the identifier itself. …
  The write specifier must be at least as restrictive as the read specifier
  — you cannot write to a variable that is privately readable but publicly
  writable". Example 15, lines 523-534: `var<protected> Score<public>:int`,
  `var<private> PlayerCount<public>:int`, `var<private> SessionID<internal>:string`
  and `game_state{SessionID := "s1"}` from outside the class.
- Ch. 10, lines 2073-2091: fields and methods `<private>`, `<protected>`,
  `<internal>`, `<public>`; "Default visibility is `internal` (same module
  only)."
- Ch. 9, line 29: "All struct fields are public and immutable by default."
- Ch. 11, lines 1333, 1355-1360: type aliases "can have access specifiers";
  "Only `<public>` and `<internal>` are available here. Writing
  `ProtectedAlias<protected> := float` at module scope is an error, because
  `protected` and `private` are meaningful only inside a class or an
  interface." "A type alias cannot be more public than the type it aliases."
- Ch. 16, lines 1227-1229: "Members without the `<public>` specifier are
  internal by default, so nothing outside the defining module can see
  them"; lines 1249-1251: "The same applies inside classes: `<private>` and
  `<protected>` members are not accessible outside their defining scope".
- Ch. 6, lines 1180-1182: "Nested functions **cannot** have access
  specifiers like `<public>`, `<internal>`, or `<private>`".
- Ch. 18, lines 200-202: increasing accessibility is allowed, reducing it is
  forbidden, "Nor can you make constructors less accessible" (a rule between
  published versions of a package, which openverse does not have).

## The rules

### What each specifier admits

A specifier is written on a definition, which is *at* a place: a module (the
top level is the program's root module) or a class, interface or struct in a
module. A use is written in code, which is *at* a module and, in a method, a
field's default or a `block:`, at a class. A specifier admits a use when:

| Specifier | Admits a use in | Sources |
|---|---|---|
| `<public>` | any code | ch. 12 lines 12, 21-23 |
| `<internal>` | code in the definition's module or a module inside it | ch. 12 line 13, 151-154; `AccessLevelInheritance.versetest:605-631` (a submodule overrides and sets an `<internal>` field of its parent module's class) |
| `<protected>` | code in the definition's class or interface, or in a class or interface below it, in any module | ch. 12 lines 67-69; `Classes/AccessSpecifiers.versetest` 98-142; `AccessLevelInheritance.versetest:91-128` |
| `<private>` | code in the definition's class or interface itself (not one below it) | ch. 12 lines 110-112; `Classes/AccessSpecifiers.versetest` 51-95; `Interfaces/AccessSpecifiers.versetest` 51-95 |
| `<scoped{M, …}>` | code in the definition's module (or inside it), or in one of the modules `M, …` (or inside them) | ch. 12 lines 195-221; `scoped.versetest` 155-185 ("automatically internal to A"), 380-385 |
| `<epic_internal>` | code of an Epic package; the tests' snippets are (see Readings) | ch. 12 line 17; `Classes/AccessSpecifiers.versetest:421` |

A use names a path, and each step of it must admit the use: `A.B.c` needs
`A`, `B` and `c` (ch. 12 lines 320-323, 455-457; `scoped.versetest` 428-485).
A member reached through a value, `X.F`, is reached through its class: it
admits the use when `F`'s specifier does and its class (and that class's
modules) does (`scoped.versetest:448-455`, "we can't see through AC to get
there"; `SOL-5564-…:3`, a member introduced by an `<internal>` interface,
called through a `<public>` class from another module).

### Defaults

| Definition | Default | Sources |
|---|---|---|
| a module, and a module's (or the top level's) function, constant, class, interface, struct, enum or type alias | `<internal>` | ch. 12 line 13; ch. 16 lines 1227-1229; `TypeAlias.versetest:228` |
| a field or method of a class or interface | `<internal>` | ch. 10 line 2091; `Classes/AccessSpecifiers.versetest` 212-218 |
| a struct's field | `<public>` (any other access specifier is refused, 3594) | ch. 9 line 29; `v1-PublicStructFields.versetest` 5-23, 27-28 |
| a class's, interface's or struct's constructor (`class<…>`) | the type's own access: it restricts nothing more | `Classes/AccessSpecifiers.versetest` 411-422 (`<public> := class{X<internal>:int}` is refused, `<internal> := class{X<internal>:int}` is not) |
| the write access of `var` | that of reading: it restricts nothing more | `VarAccessSpecifiers.versetest:224` ("var is public by default, so it doesn't restrict field access unless we narrow it") |
| an override | the access of what it overrides (it may not write one) | `AccessLevelInheritance.versetest` 159-179, 257-313 |

### Where each may be written

| Place | Allowed | Refused (code) | Sources |
|---|---|---|---|
| a module | `<public>`, `<internal>`, `<scoped>`, `<epic_internal>` | `<private>`, `<protected>` (3594) | `Modules/Module.versetest:36` |
| a function, constant, class, interface, struct, enum or alias of a module or the top level | `<public>`, `<internal>`, `<scoped>`, `<epic_internal>` | `<protected>`, `<private>` (3594) | `ModuleDefinitions.versetest` 129, 130, 315, 316; `Modules/AccessSpecifiers.versetest` 369-410; ch. 11 lines 1355-1357 |
| a class's or interface's field or method | all six | | `Classes/AccessSpecifiers.versetest`; `Interfaces/AccessSpecifiers.versetest` |
| `var<…>` of a class's or interface's field | all six (write access) | | ch. 12 lines 513-549; `VarAccessSpecifiers.versetest` |
| a struct's field | `<public>` | the others (3594) | `v1-PublicStructFields.versetest` 5-17 |
| after `class` (its constructor) | `<public>`, `<internal>`, `<protected>`, `<epic_internal>` | `<private>` (3594) | `ArchetypeAccessSpecifiers.versetest` 47-50; `Classes/AccessSpecifiers.versetest` 435-453 |
| after `struct` or `interface` | `<public>`, `<internal>`, `<epic_internal>` | `<protected>`, `<private>` (3594) | `ArchetypeAccessSpecifiers.versetest` 43-46; `Classes/AccessSpecifiers.versetest` 455-465; `InterfaceAccessVisibility.versetest` 36-40 |
| an override (`X<override>`, `var<…> X<override>`) | none | any (3650) | `AccessLevelInheritance.versetest` (27 cases) |
| a local, a nested function, a parameter | none | 3661 (3641 on a local `var<…>`) | `AccessSpecifiersDisallowedOnLocalVars.versetest`; `NestedFunctions.versetest` 5-17; `VarAccessSpecifiers.versetest:180`; ch. 6 lines 1180-1182 |
| one place, two access specifiers | | 3543 (two different), 3642 (one twice, or two `<scoped>`) | `Classes/AccessSpecifiers.versetest` 350-366; `VarAccessSpecifiers.versetest` 108-114; `scoped.versetest` 91-101; ch. 12 lines 362-379 |

Enum values take no specifier in any test or chapter.

### Overrides

An override is the member it overrides, so it has that member's access, for
reading and for writing: an override that writes an access specifier, on its
name or on its `var`, is refused (3650) whether the specifier is wider
(`Foo<public><override>` over `<protected>`, `AccessLevelInheritance.versetest:23`),
narrower (`:13`, `:229` "Can't narrow scope") or the same
(`var<Scoped_M1_M2_M3> Field<override>` over the same, `:524`). An override of
a member its class cannot see is refused (3593): a `<private>` one (`:33`,
`:751`), an `<internal>` one of another module (`:43`, `:823`), a `<scoped>`
one not granted to its module (`:196`). The override keeps the access it
takes from what it overrides: in `:159-179` an override in `M2` of a field
`<Scoped_M1_M2>` is read from `M1` through the subclass.

### Separate read and write access

`var<w> X<r>:t`: `X` is read where `<r>` admits and set where both admit
(ch. 12 lines 513-549). A `set` that reading admits and writing does not is
refused as a `set` of what is no `var` (3509: `VarAccessSpecifiers.versetest`
37, 116, 136, 166; `AccessLevelInheritance.versetest:315`); one that reading
does not admit is refused for reading (3593: `VarAccessSpecifiers.versetest`
144, 173). The write specifier is at least as restrictive as the read one
(ch. 12 lines 546-549). A construction gives a field a value where reading
admits it (ch. 12 example 15: `game_state{SessionID := "s1"}` with
`var<private> SessionID<internal>`; `VarAccessSpecifiers.versetest:37`).

### Constructors

`c<a> := class<k>{…}`: constructing `c{…}` and naming `c` as a parent need
both `<a>` and `<k>`. `my_class<public> := class<internal>{…}` is a public
type that only its module constructs or extends: from outside it is used as
a type and through a public function that makes one
(`ArchetypeAccessSpecifiers.versetest` 3-40: "class<internal> forces folks
outside the owning module to use a constructor function"; "you cannot get
around the restrictions by using subclassing", line 22). A `<protected>`
constructor is used by the classes below (`Classes/AccessSpecifiers.versetest`
435-445). An `interface<internal>` cannot be implemented outside its module,
but an interface or class of its module that extends it can be
(`InterfaceAccessVisibility.versetest` 9-27, 78-87). Each field given in a
construction must be readable there.

### Consistency: a definition exposes nothing less visible than itself

"Dependencies of definitions are as accessible as the definitions themselves"
(`DigestVisibility.versetest:3-4`, comment). Every definition has an
effective visibility: what its own specifier admits, within what its class
and modules admit (`DigestVisibility.versetest` 33-61: a `<public>` function
in an internal module or class may name an internal class). Then:

1. **Signatures.** Each type a definition's signature names is at least as
   visible as the definition (error 3593): a function's or method's
   parameter and result types (`DigestVisibility.versetest` 20, 27, 121-157),
   a constant's or field's type, through `?`, `[]`, maps, tuples and
   function types (72-106), a type alias's type (ch. 11 line 1360;
   `TypeAlias.versetest` 228-239; `DigestVisibility.versetest:115`), a
   struct's field (`DigestVisibility.versetest:156`), and a parametric
   type's arguments (`ParametricTypes.versetest` 1260, 1272; FN36.00). A
   `<protected>` method of a `<public>` class reaches every class below it,
   in any module, so it may not name an internal type
   (`DigestVisibility.versetest:27`); a `<private>` one may
   (`DigestVisibility.versetest:130`). An override is judged in its own
   class (`AccessLevelInheritance.versetest:863-873`: an `<internal>` class's
   override of a `<public>` field may have an `<internal>` type).
2. **Fields with no value.** A class's or interface's field with no default
   is at least as visible as its constructor, which must give it one
   (`Classes/AccessSpecifiers.versetest` 410-433; `Interfaces/AccessSpecifiers.versetest`
   283-311; `Classes/AccessSpecifiers.versetest` 205-235; FN40.00 for
   interfaces). A default waives it (`:430-433`).
3. **`var` write access** is at least as restrictive as read access
   (ch. 12 lines 546-549).

No test or chapter refuses a `<public>` class whose parent is internal:
`SOL-5564-…:3` (`c<public> := class(i)` with `i<internal> := interface`)
gives one error, which the call from another module of a member `i`
introduces accounts for (Readings).

### The visibility order

A specifier written at a place denotes a set of code: its *audience*
(above). One specifier is **at least as visible as** another when its
audience contains the other's. A definition's **effective audience** is the
intersection of its own and those of the definitions it is in (its class,
its modules). Both kinds of rule use the order:

- access: a use is admitted when its code is in the effective audience of
  every definition its path names;
- consistency: a definition's effective audience is contained in that of
  every type its signature names, a field's with no value contains its
  constructor's, and `var`'s write audience is contained in its read one.

At one place, with `M` the place's module and `c` its class:

```
                <public>
             /      |       \
   <epic_internal>  |    <protected> (c and below, any module)
          |         |        |
   <scoped{G}> (M and G)     |
          |                  |
     <internal> (M)          |
             \              /
              <private> (c)
```

`<private>` ⊆ `<internal>` (a class's code is in its module) and ⊆
`<protected>`; `<internal>` ⊆ `<scoped{G}>` (a scope includes its own
module); `<protected>` is comparable with neither `<internal>` nor
`<scoped>` nor `<epic_internal>` (`DigestVisibility.versetest:127`:
a `<protected>` method of a `<public>` class may not name an
`<epic_internal>` class). Across places, `<internal>` at `M` is contained in
`<internal>` at `N` when `M` is `N` or inside it; `<protected>` at `c` in
`<protected>` at `d` when `c` is below `d`.

## Error codes

| Code | Meaning | Example |
|---|---|---|
| 3593 | a use its path's specifiers do not admit; a definition that exposes a less visible one | `Classes/AccessSpecifiers.versetest:62`: `param.myMember` of a `<private>` member from another class; `TypeAlias.versetest:228`: `c := class{}; a<public> := c` |
| 3594 | an access specifier not allowed on that kind of definition | `Modules/Module.versetest:36`: `M<private> := module {}`; `ArchetypeAccessSpecifiers.versetest:43`: `struct<protected>` |
| 3543 | two different access specifiers in one place | `Classes/AccessSpecifiers.versetest:355`: `myFunction<public><internal>()` |
| 3642 | one specifier twice, or two `<scoped>` | `VarAccessSpecifiers.versetest:112`: `var<public><public> Field:int`; `scoped.versetest:91` |
| 3650 | an override that writes an access specifier | `AccessLevelInheritance.versetest:13`: `Foo<private><override>:int` |
| 3509 | a `set` that reading admits and writing does not | `VarAccessSpecifiers.versetest:37`: `set X.IntArray` of `var<private> IntArray<public>` |
| 3641 | an access specifier on a local's `var` | `VarAccessSpecifiers.versetest:180`: `var<internal> X:int = 42` in a function |
| 3661 | a specifier on a local definition or nested function | `AccessSpecifiersDisallowedOnLocalVars.versetest:5`; `NestedFunctions.versetest:5` |
| 3506 | `scoped{M}` of no module | `scoped.versetest:40` |
| 3587 | `scoped{/path}` of no package | `scoped.versetest:104` |
| 3588 | two definitions a use admits, of one name | `SOL-7898-…:16`; `scoped.versetest:316` |
| 3590, 3552 | a scope used as a class or a type | `scoped.versetest` 487, 491 |
| 3596 | (with 3593) `<intrinsic>`, an attribute for the Verse package's own code | `Attributes/intrinsic.versetest` 3-9 |
| 2016 | a warning of Verse version 0: a struct field not public | `v1-PublicStructFields.versetest:4` |

## Unreleased, version-gated and VM-specific

- Nothing of chapter 12's access specifiers is marked unreleased; its
  annotations `@deprecated`, `@experimental`, custom attributes and getter
  and setter accessors are marked "Internal Feature" (lines 607, 667, 740,
  851), and are not access specifiers.
- `<epic_internal>` is "only usable by Epic-authored code" (ch. 12 line 17);
  a non-Epic package (`/localhost`) that writes one is refused
  (`Classes/AccessSpecifiers.versetest:301-309`, `Modules/AccessSpecifiers.versetest`,
  `InterfaceAccessVisibility.versetest:51`).
- Version gates, by the package's `UploadedAtFNVersion`: the use in
  `SOL-5564-…` is an error from 28.10 on; parametric types' arguments are
  checked from 36.00 on (`FN36.00-…`, `ParametricTypes.versetest:1265`);
  interface fields with no value against the constructor from 40.00 on
  (`FN40.00-…`). Struct fields became public, and their other specifiers
  errors, in Verse version 1 (`v1-PublicStructFields.versetest`). openverse
  takes the latest of each, as the tests do without a version.
- No access test is tagged `bp_vm_only` or `verse_vm_only`.

## Where the prose and the tests disagree

1. **Overrides.** Prose, ch. 12 lines 384-386: "overriding members in
   subclasses can maintain or narrow that access, following normal
   inheritance rules"; example 11, lines 398-399: `ComputeValue<override>():int = 100
   # Now internal to this module`. Tests: `AccessLevelInheritance.versetest:229-244`,
   `Field<override><Scoped_M1_M2>:int = 50` over `<Scoped_M1_M2_M3>`,
   "# Can't narrow scope", error 3650; `:524-537`, the same scope written
   again, 3650; `:159-179`, an override with no specifier keeps the scope
   ("# by default, this is only accessible in M1/M2") and is read from `M1`.
   openverse follows the tests: an override has its member's access and
   writes none.
2. **`<private>` on a struct's field.** Prose, ch. 12 line 14: `<private>` is
   "Local to class/struct". Tests: `v1-PublicStructFields.versetest:5`,
   `s := struct{X<private>:int=0}` is error 3594 in Verse version 1 (and a
   warning, 2016, in version 0). Ch. 9 line 29 agrees with the tests: "All
   struct fields are public". openverse follows the tests.
3. **`<epic_internal>`.** Prose, ch. 12 line 17: "only usable by
   Epic-authored code". Tests: the snippets use it freely and it orders
   between `<internal>` and `<public>` (`Classes/AccessSpecifiers.versetest:421`,
   "access_test_c10 is in epic_internal scope itself"; `:424-433`;
   `DigestVisibility.versetest` 121-157); only a package that is not Epic's
   is refused (`:301-309`). Not a contradiction (the test runner is Epic
   code), but openverse, which has no packages, must choose (Readings).

## Readings openverse takes

- **The program is one package, in the tests' scope.** openverse has no
  packages, so a program is its own package, its top level the root
  module, and it stands where the Book's test snippets stand: an
  Epic-internal scope. `<epic_internal>` may be written; it admits all of
  the program, and orders above `<scoped>` and `<internal>`, below
  `<public>` (a `<public>` definition reaches code no package of Epic's
  writes). Refusing it outright, as a user package would be, would refuse
  the tests' valid uses (`Classes/AccessSpecifiers.versetest` 422-433).
- **`scoped{…}` names modules of the program.** A path (`scoped{/Verse.org}`)
  names a package, which openverse has none of: refused with a message.
- **A member reached through a value** is admitted where its declaration
  (the one that introduces it, which overrides inherit) is reachable: its
  specifier within its class's and modules' (`SOL-5564-…:3`;
  `scoped.versetest:448`). That one test does not say whether the
  Book's compiler refuses the call or the `<public>` override; the call is
  the reading that also covers `scoped.versetest:448`, where nothing is
  overridden.
- **Overloads of one name in one class or module** have one access (an
  openverse rule that the modules' renaming already had for modules): no
  test gives two overloads of one name different access in one scope.

## Design

Two kinds of rule, both properties of the program once every name is
resolved, neither changing what is generated:

- **access**: a use of a name is admitted from the code it is written in;
- **consistency**: a definition's signature exposes nothing less visible
  than the definition.

**One order.** `Front/Access.lean` defines the audience of a specifier at a
place (`Access.Audience`: everyone, Epic code, a module and what is inside
it, a scope's modules, a class and the classes below it, a class), a
definition's effective audience (the list of audiences of it and the
definitions around it, an intersection), whether code at a site is in one
(`admits`), and when one is contained in another (`within`). Every check
below asks these two questions and nothing else.

**Specifiers in the tree.** Each definition keeps the specifiers written on
it: a constant's, a struct's, an enum's, an alias's and a module's marker's
(`STop.const` gains its list), a class's or interface's name (`STop.classDef`
gains `nameSpecs`, beside its own specifiers after `class`), a field's and
its `var`'s (`SField`, a structure, for classes and structs alike); a
function's and method's were kept already. The workarounds go: `$public:`
markers (the modules' renaming reads a member's specifiers), `$final:F`
among a class's specifiers (a field's own specifiers say it), and a class's
list of overriding fields (its fields' specifiers say it).

**Where each rule is checked.**

1. *Where a specifier may be written* (3594, 3543, 3642, 3650, a local's):
   the parser and `EffectPolicy.specifierPlaces`, the one table of where each
   specifier may be written, which gains the access specifiers and the places
   a module, a struct's field and `var`.
2. *Module members* are resolved by the modules' renaming
   (`Front/Modules.lean`), which knows the code each use is written in: every
   level of a path (`M.F`, `A.B.c`, a qualifier, a `using{A.B}`) and every
   member a `using` opens must admit the use; a member a `using` opens that
   the use cannot see does not make a name ambiguous (`SOL-7898-…:36`).
3. *Constructions, parents and overrides* are names of classes and members
   known without types: `Access.check`, run on the resolved program, finds
   the class a construction `c{…}` or a parent names and the fields given,
   and what an override overrides, and checks them at the code they are
   written in.
4. *Members reached through a value* (`X.F`, `X.M(…)`, `set X.F`, a member
   used bare in a method) need `X`'s class, which only the elaborator knows.
   It asks `Access` where it resolves the member, with the code the use is
   written in found by position: `Access.Sites`, made from the resolved
   source before any function is inlined or generated, maps a position to
   the source definition it is in (its module and class), so a member read in
   a function that is later inlined elsewhere is still judged where it was
   written. Code the compiler writes (helpers, function-value classes)
   reaches no member it could not, and a use whose position is in no source
   definition is the compiler's.
5. *Consistency* is `Access.checkConsistency`, on the resolved program before
   type aliases are written out (an alias is a definition with an access of
   its own): for each definition, the types its signature names, each
   containing its effective audience; each field with no value against its
   class's constructor; each `var`'s write access against its read access.

Errors follow the phases (DESIGN.md, "Elaboration in phases"): placement
with the parser and the effect policy; module members with the renaming;
constructions, parents, overrides and consistency right after it, before
type aliases are written out; members reached through values with the
elaboration of functions.
