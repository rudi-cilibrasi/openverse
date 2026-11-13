# Qualified names

The rules openverse takes for qualified names `(q:)x`, every form the Book
of Verse writes, where each may be written, what it means and what is an
error; the readings openverse had to choose; how qualification meets the
Book's shadowing rule, which openverse now follows; and the design, one resolver for every qualifier.
[LANGUAGE.md](../LANGUAGE.md#qualified-names) states the rules for users;
[DESIGN.md](../DESIGN.md#qualified-names-one-resolver-for-every-qualifier)
says how they are built.

## Sources

- The [Book of Verse at `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs):
  chapter 9, "Explicit Qualification" (`docs/09_structs_enums.md` lines
  507-551); chapter 10, "Shadowing and Qualification" through "Restrictions"
  (`docs/10_classes_interfaces.md` lines 887-1191); chapter 16, "Qualified
  Names" (`docs/16_modules.md` lines 549-608), "Local Qualifiers" (lines
  687-787), "Automatic Qualification" (lines 789-984, marked "Unreleased
  Feature") and "Explicit Qualification" (lines 986-1015).
- The same snapshot's tests, cited by line: `Tests/QualifiedIdentifier.versetest`,
  `ShadowDefinition.versetest`, `Pointers.versetest` (45-58), `Type.versetest`,
  `TypeAlias.versetest`, `Super.versetest`, `Enum.versetest`, `Effects.versetest`
  (352-363), `Modules/Module.versetest`, `Modules/ModuleDefinitions.versetest`,
  `Classes/QualifiedMethodInheritance.versetest`, `InterfaceWithFields.versetest`,
  `DefaultNamed.versetest` (46-53), and in `Bugs/`: `SOL-3104`, `SOL-3564`,
  `SOL-7503`, `SOL-7579`, `SOL-7778`, `FORT-951162`; `Versions/FN41.00/FN41.00-FirstAdded.versetest`.
- Retrieved 2026-11-13. No Epic source was read and no Epic compiler was run;
  the [survey](book-test-conformance.md) compares openverse with the tests'
  expectations.

## Quotations

- Ch. 16, lines 557-559: "when you want to explicitly specify the scope of
  an identifier, use a qualified access expression using parentheses and a
  colon". Example 14 (lines 562-571): in `mixer`, which has `using { audio }`,
  `(local:)Volume:int = 1` and `(local:)Volume + (audio:)Volume   # 1 + 5`.
  Lines 577-580: a name that collides "must be written
  `MyModule.(MyModule:)Last(X)` to select yours".
- Ch. 16, lines 689-692: "The `(local:)` qualifier can disambiguate
  identifiers within functions. This is critical for evolution
  compatibility—when external modules add new public definitions after your
  code is published, `(local:)` ensures your local definitions take
  precedence." Example 18 (lines 707-719): without it, `ShadowX:float = 0.0`
  "conflicts with ExternalModule.ShadowX"; with it, `(local:)ShadowX:float =
  0.0` and `(local:)ShadowX   # returns 0.0, not 10`.
- Ch. 16, lines 725-727: "The qualifier applies to function parameters, data
  definitions in a function body, `for` loop variables, `if` conditions,
  block scopes and class blocks". Lines 764-766: "you currently cannot
  redefine a `(local:)` qualified identifier in a nested block."
- Ch. 16, lines 864-870 (Automatic Qualification, unreleased): "`int →
  (/Verse.org/Verse:)int`, `float → …`, `string`, `logic`, `message`";
  lines 966-970: "The same happens on a smaller scale when a local variable
  has the same name as a module member: qualification is what distinguishes
  `(/MyModule:)Value` from `(local:)Value`."
- Ch. 16, line 934: "Even with automatic qualification, nested definitions
  cannot shadow outer definitions with the same name. If you want to
  intentionally shadow something, you must use explicit qualifiers to make
  your intent clear."
- Ch. 10, lines 894-896: "In most contexts, you **cannot redefine names**
  that already exist in an enclosing scope." Lines 966-976 (example 027):
  `c := class: (c:)F(X:int):int = X + 2` beside a top-level `F`; "`c{}.(c:)F(10)
  = 12      # explicit qualification, optional here`"; "The `(c:)` qualifier
  indicates this `F` is defined specifically in the `c` class context".
- Ch. 10, lines 1014-1024: "`F<override>` without qualifier: Overrides the
  inherited `F`"; "`(e:)F` without `<override>`: Defines a **new** `F`
  specific to `e`"; "There is no rule that the nearer or the more derived
  definition wins: an unqualified `E.F(10)` matches both".
- Ch. 10, lines 1050-1052: "`(super:)F(X)` within the qualified method calls
  the parent class's implementation of that same qualified method."
- Ch. 10, lines 1158-1166: "A qualifier only says which `F` is meant among
  the ones already in scope; it does not itself bring anything into scope.
  Drop the `using` declarations and `(Top.M:)F(0)` does not become ambiguous,
  it becomes an unknown identifier."
- Ch. 10, lines 1189-1191: "Currently, there is no `(local:)` qualifier to
  disambiguate" a local named like a member; the tests disagree
  (`QualifiedIdentifier.versetest:446-465`, `SOL-7579`), and openverse follows
  the tests.
- Ch. 9, lines 528-531: "The syntax `(enum_name:)enumerator` explicitly
  qualifies the enumerator, preventing conflicts with outer-scope symbols.
  Qualification also allows you to use reserved words and keywords as enum
  values".

## The rules, form by form

A qualifier `(q:)` names a **scope**: a module, a class or interface, a
struct or enum, the locals of the code it is written in (`local`), the
implementation above a method (`super`), or a package by its path. Each row
says where the form may be written, what it means and what the tests refuse.
"Def" is a definition's head, "use" a name in an expression or a type.

| Form | Where | Meaning | Refused (tests' code) | Sources |
|---|---|---|---|---|
| `(M:)x`, `(A.B:)x` | use | the member `x` of the module, found as a name is | `using{(A:)B}` with no `A` (3506) | ch. 16 ex. 14, 26; ch. 10 ex. 032; `QualifiedIdentifier:78`; `ShadowDefinition:236-258` |
| `(M:)x` | def in `M` | `x`, a member of `M` | a qualifier that is not the enclosing module: `(D:)C := class{}` (3506), `(M.f:)X` (3612) | `Modules/Module:192-209`; `ShadowDefinition:209-231`; `ParametricFunctions:537-690`; `TypeAlias:161-166` |
| `M.(M:)x` | use | `M`'s `x`: the qualifier names the module before the dot | another module | ch. 16 lines 577-580; `generators.versetest:251` |
| `X.(M:)F(…)` | use, `X` a value | `M`'s extension method `F` of `X` (ch. 6), selected among those in scope | `M` has none | ch. 16 lines 577-580 (the collision it resolves) |
| `(c:)m` | def in class `c` | a member `m` of `c`; when no class above has an `m`, it is `m` | | ch. 10 ex. 027; `ShadowDefinition:9-17`; `FORT-951162`; `SOL-3104:5-12`; `ModuleDefinitions:59` |
| `(c:)m` | def in `c`, inheriting an `m` | a second `m`, beside the inherited one; a bare `X.m` is then ambiguous | `(c2:)F<override>` (3523) | ch. 10 lines 978-1024; `ShadowDefinition:98-116` |
| `(r:)M<override>` | def in a class below `r` | implements the `M` that `r` introduces (its slot) | `r` above that does not introduce `M` (3591, 3523); `r` not above (3612) | ch. 10 ex. 029-031; `ShadowDefinition:64-96`; `QualifiedMethodInheritance:162-187` |
| `(c:)F:t` | field def in `c` | the field `F` | | `QualifiedIdentifier:15`; `ModuleDefinitions:220-222` |
| `(c:)m`, `Self.(c:)m`, `X.(c:)m` | use | the member `m` that `c` introduces, of an `X` below `c` | a class that inherits or overrides it (3506) | `QualifiedIdentifier:10-11`; `SOL-3564:90-150, 176`; `ShadowDefinition:261-268`; `VarSet:106-109` |
| `(super:)M(…)` | use, in an override | the implementation above | not in an override of `M` (3612), on a value, an enum, a macro (3506, 3560, 3552) | ch. 10 lines 1026-1052; `Super.versetest` |
| `(e:)v` | value def in enum `e` | the value `v`, which may be a reserved word or a keyword | another qualifier | ch. 9 lines 507-551; `QualifiedIdentifier:305-321`; `SOL-7778`; `Enum:107-114` |
| `(e:)v` | use | `e.v` | | ch. 9 lines 516-519, 543-547 |
| `(s:)f` | field def in struct `s` | the field `f` | | `SOL-7503` (with a path) |
| `(local:)x` | a local's, a `var`'s, a `for` variable's or a parameter's def, in any code: a function's body, a class block, a constant's value | a local, which may take the name of a definition outside the code | a member's def: module, class, struct, interface, enum value (3612); `using{(local:)M}` (3612); a named parameter `?(local:)X` (3552); a local of the same name in scope, nested (3532); a type parameter's name (3588, 3532) | ch. 16 lines 687-787; `QualifiedIdentifier:175-484`; `Pointers:45-58`; `SOL-7579`; `DefaultNamed:46-53` |
| `(local:)x` | use | the local `x` of the enclosing code, written `(local:)` or not | no such local (3506) | ch. 16 ex. 18-20; `QualifiedIdentifier:378-381` |
| `(/p:)x` | use, def, type | `x` in the package or module at path `/p` | an unknown path (3587) | ch. 16 lines 815-870; `QualifiedIdentifier:81-173, 468-483, 486-559` |
| `using{(A:)B}` | a module's using | `using{A.B}` | `(local:)` (3612), unknown (3506) | `QualifiedIdentifier:57-79, 297-300` |

**What is an error.** A qualifier is refused when it names nothing (3506), or
names a scope that does not hold the definition: for a definition, a scope
other than the one it is written in (or, for an override, other than the
class or interface that introduces the member; 3612, 3591, 3523); for a use,
a scope that does not define the name itself, as `(base_class:)Func2()` when
`basest_class` defines `Func2` (`SOL-3564:90`, 3506). A **redundant**
qualifier is no error: `c{}.(c:)F(10)` is "optional here" (ch. 10, line 965),
and ch. 16's example 26 writes `(GameSystem:)Value` inside `GameSystem`. A
reserved name stays reserved when qualified (`(ModuleA:)local`,
`(/A/ModuleA:)spawn`, `(m:)true`, `(m:)suspends`: 3514,
`QualifiedIdentifier:239-260, 485-490`, `Enum:56-59`, `Effects:352-363`), but
an enum's value may take one (ch. 9).

**A bare name where a qualified definition shadows another.** The tests
refuse a bare use that a qualified definition and an outer definition both
give, as ambiguous: `x:int=42` and a class's `(C:)x:int`, then `x` in the
class's method (`ModuleDefinitions:88, 238`, 3588; with functions, `:71`,
3518); a top-level `A` and `(local:)A := A+1` (`FN41.00-FirstAdded`,
3588 from version 41.00). Qualification makes the inner definition possible;
it does not make it win.

## Readings openverse takes

1. **A qualifier needs no `using`.** Ch. 10 (lines 1158-1166): a qualifier
   "does not itself bring anything into scope", so `(Top.M:)F(0)` without a
   `using` is an unknown identifier. openverse's `(M:)F` has been `M.F` since
   #145: the qualifier is found as any name is (from the use's scope
   outward), then `F` is looked up in exactly that module, with `M.F`'s
   visibility. No test of the Book exercises the difference (the chapter's
   own example comment, `Use59`, is not in `Tests/`); openverse accepts a
   superset, and keeping #145's programs is worth more than refusing them.
2. **A module's qualified member used bare inside the module.** The Book
   resolves a bare name that a module's `(M:)x` and an outer `x` both give
   among both, by their parameters, refusing it when both fit
   (`ModuleDefinitions:62, 78, 229`, all `vmodule`); `ParametricFunctions`
   uses its module's `(M:)class2(t:type)` bare, as `class2(tuple(int, t))`,
   beside a top-level `class2` that takes no type argument, and expects it to
   work. openverse takes the inner one (a module's own definitions come first
   in its lookup); the tests' only such use is one the inner fits. Inside a
   class and for `(local:)`, where the tests refuse the bare use, openverse
   refuses it too.
3. **A local's scope starts after its definition**, for `(local:)` locals as
   for openverse's others: in `(local:)A := A+1`, `A` is the outer one. The
   Book's version 41.00 calls that `A` ambiguous (`FN41.00-FirstAdded.versetest`,
   a `vpackage` test), which reads the local as visible in its own value.
4. **Paths.** openverse has no packages: its top level has no path and no
   name, and its modules are named `M` or `A.B`. It stands in for
   `/Verse.org/Verse` with its built-in types, which ch. 16 (lines 864-870)
   names: `(/Verse.org/Verse:)int` is `int`. Any other path, an engine
   module's (`/Verse.org/Random`) or the test runner's own top level
   (`/Verse.org/VerseTests/…`, `(VerseTests:)FE`), is refused with a message
   that says openverse has no module there. Which standard module each
   built-in function belongs to is not pinned, so `(/Verse.org/Verse:)Print`
   is refused as no type.
5. **Members of one name.** A class that inherits an `m` and writes `(c:)m`
   has two members `m` (ch. 10, "Methods with Same Name"; for fields,
   `InterfaceWithFields:229-262, 552-566`). openverse keeps one member of a
   name per class (a field of two declarers is merged, a method is one
   slot unless an interface introduces it again), so it refuses the second
   one, and refuses `X.(c:)F` when `X`'s class has fields `F` of two
   declarers, rather than read the merged one.

## Shadowing

The owner has since decided to follow the Book here too ("for everything we
go by the book for now"), so openverse's documented inner-first reading,
under which a member could take the name of an enclosing definition, is
gone. The rule, as the Book's prose and tests pin it:

- **The rule.** "In most contexts, you cannot redefine names that already
  exist in an enclosing scope. This applies to functions, variables,
  classes, interfaces, and modules" (ch. 10, lines 894-896); "The
  prohibition holds regardless of definition order" (line 951); "nested
  definitions cannot shadow outer definitions with the same name" (ch. 16,
  line 934). openverse checks it in `checkNoShadowing`, beside the "defined
  once in its scope" check (`checkDefinedOnce`, `admitSource`).
- **Which scopes.** The top level and the modules nest; a class, an
  interface, a struct and an enum are scopes inside the one they are defined
  in, and a function's parameters and locals inside the function's. Sibling
  scopes do not meet: two functions' locals, two loops' variables
  (`QualifiedIdentifier:197-217`), a field of one class and a parameter of
  another function (no test refuses them).
- **Which definitions.** Every kind: a module's member or a module named like
  a definition of a module around it or of the top level
  (`ShadowDefinition:270-299, 331-341`, `Modules/Module:220-226`,
  `Enum.versetest:121`); a class's or an interface's field or method named
  like a definition of the scope the type is defined in or around it, the
  type itself included (`ShadowDefinition:4, 296, 328-329`,
  `Overloading.versetest:171`: `f := class: f():f`); an enum's value named
  like the enum or a definition around it (`QualifiedIdentifier:310`); a
  struct's field likewise (no test; the prose's "variables", and a field is
  a class's data member's counterpart); a parameter (`ShadowDefinition:356`,
  a `vpackage` test); a local (`QualifiedIdentifier:186-195`,
  `ShadowDefinition:319-325`, which openverse already refused where names are
  resolved).
- **What counts as the same name.** One spelling. Functions are the one
  exception: they overload across scopes as in one, so a function, a method
  or a parameter of a function type may take the name of a function around
  it when no call fits both (`Overloading.versetest:41-43`, "Test overloading
  a function across different scopes": `f():void` beside a parameter
  `f(x:int):void`, and beside a method `f(x:int):void`); with parameters a
  call could fit both they are refused (`ShadowDefinition:4`: `F(X:int):int`
  and a method `F(X:int):int`; `:350-353`, a module's `F():void`). A
  function and anything else of one name are refused (a value, a type, a
  module: `ShadowDefinition:328-341`, `Overloading.versetest:162-168`).
  openverse checks a function or a method against an enclosing function
  where it checks overloads, with the same distinctness test
  (`checkSignatures`); a parameter of a function type it lets take the name
  unchecked (a reading: in the function's body the name is the parameter).
- **What is exempt.** A qualified definition, `(M:)x`, `(c:)m`, `(e:)v`,
  `(local:)X`: "If you want to intentionally shadow something, you must use
  explicit qualifiers to make your intent clear" (ch. 16, line 934;
  `Modules/Module:228-237`). An override (`M<override>`, `(r:)M<override>`,
  a field's `F<override>`): it implements an inherited member, it defines no
  name. openverse's entry point `Main`, which the Book does not have: a
  module's `Main` shadows nothing (the Book's runner has no top-level `Main`;
  `Operators/LogicalOr.versetest:153-162` defines one in a module). Not
  covered: a member named like a public member of a module a `using` opens
  (the tests that pin it are `vmodule` ones), and a definition named like a
  built-in other than a reserved name (`enum{public}`,
  `QualifiedIdentifier:315`, is the one test; openverse knows no definition
  named `public`).
- **How a qualifier lifts it.** The inner definition written `(q:)x`, `q`
  its own scope, is accepted; a bare `x` where both are visible is then
  ambiguous in a class's code and for `(local:)` (above), and the inner one
  inside a module (reading 2). openverse's message names both definitions
  and the qualifier to write: "the field 'Limit' of thing has the name of
  the constant Limit (2:0): Verse does not allow shadowing (Book of Verse
  ch. 10); rename one, or qualify this one, (thing:)Limit".
- **Prose and tests.** They agree where both speak. The prose is silent on
  functions overloading across scopes, which the tests allow (above), and on
  struct fields, which openverse treats as class fields; ch. 10's
  "Restrictions" (lines 1189-1191) says there is no `(local:)` for a local
  named like a member, which the tests contradict (`QualifiedIdentifier:446-465`,
  `SOL-7579`): openverse follows the tests there.

## Design: one resolver for every qualifier

The rules above reduce to one statement: **a qualifier names a scope; a
qualified name is looked up in exactly that scope and nowhere else; a
qualified definition's qualifier names where it is defined** — its own
scope for a new definition, and, for an override, the class or interface
that introduces the member it implements. Then `(local:)` is the scope of
the enclosing code's locals, a path is a package's scope, and `(super:)` the
scope above the method being overridden.

It holds for every form the tests write, with two qualifications. Ambiguity
is not the qualifier's: it belongs to bare names (above). And "the scope that
defines it" for a class member is the class or interface that *introduces*
it: an override implements a member another scope defines, which is why
`(base_class:)Func()` is refused when `base_class` overrides `Func`
(`SOL-3564:107`), and why `(r:)M<override>` names `r`.

openverse's modules are a renaming before elaboration (`Front/Modules.lean`),
which already resolved `(M:)F`, and the classes' elaboration resolved
`(i:)M<override>`, `X.(i:)M(…)` and `(super:)`. The resolver extends the
former:

- **One function decides what a qualifier names** (`Qual`,
  `Resolver.qualifier`): `local`, `super`, a path, or a module (and its
  submodules), else a type, found as a name is. Every qualifier the parser
  reads — a use, a definition's head, a member's or an enum value's or a
  struct field's name, a local, a parameter, a `using` — goes through it.
- **Each site then looks up or checks in that scope.** A use `(M:)x` becomes
  `M::x` (as `M.x` did); `(local:)x` becomes the local; `(e:)v` becomes
  `e.v`; `(c:)F` of `Self` becomes `Self.F` when `c` declares the field.
  A class-scoped method stays `(c:)M` for the classes' elaboration, which knows
  what each class introduces (the slots of #70): a qualified call now also
  checks that `c` introduces `M`. A definition's qualifier must name its
  scope; it is then dropped (`(M:)x` is `M::x`, `(c:)m` is `m`, `(e:)v` is
  `v`), so nothing after the pass knows it was written.
- **`(local:)`** needs the locals in scope, which the renaming did not track
  (no local could shadow what it renames). It now walks a body's sequences
  (a block, an `if`'s conditions, a `for`'s clauses) with the locals defined
  so far, and gives a `(local:)` local the name `(local:)x`, which no other
  name spells, so the elaborator's own checks see no shadowing.

The three existing forms go through the resolver: `(M:)F` is its module case;
`(i:)M` and `X.(i:)M` have their qualifier resolved by it (`(i:)` was a type
name resolved by `Resolver.ty` before; `Qual.type` gives the same name); and
`(super:)` is its `super` case, which leaves the call to the classes'
elaboration, as before. On the suites and the frozen corpus (5,426 programs)
no bytecode and no message changed.
