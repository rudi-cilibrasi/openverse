# Attributes

The rules openverse takes for attributes, `@name` before a definition: their
syntax and where they may be written, the built-in ones and what each means,
custom attributes (classes below `attribute`) and their scopes, what makes a
use valid or an error (the codes the Book's tests give), and whether a
program can read them; then what openverse does with each.
[LANGUAGE.md](../LANGUAGE.md#attributes) states the rules for users;
[DESIGN.md](../DESIGN.md#attributes-checked-and-taken-out-first) says how
they are built.

## Sources

- The [Book of Verse at `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs):
  chapter 12, "Annotations and Metadata" (`docs/12_access.md` lines 596-848),
  and the specifiers it calls attributes in chapter 18 (`docs/18_evolution.md`
  lines 88-90, 208-211: `<castable>`, `<persistable>`).
- The same snapshot's tests, cited by line: `Tests/Attributes/Attributes.versetest`,
  `CustomAttributes.versetest`, `deprecated.versetest`, `experimental.versetest`,
  `available.versetest`, `Tests/Bugs/2021-10-05-AttributeNames.versetest`,
  `Bugs/SOL-1729-MakeAttributesForwardCompatible.versetest`, `Enum.versetest`
  (73-100, 505-592), `FlowControl/Return.versetest` (83-162),
  `FlowControl/Reachability.versetest:94`, `Function.versetest` (105-114),
  `TimSyntax.versetest` (137-175), `Roundtrip/Comments.versetest` (119-145),
  `Roundtrip/KnownBugs.versetest:62`.

No Epic compiler was run and no Epic source code was read.

## Quotations

- Ch. 12, 598-601: "Verse provides an annotation system for attaching
  metadata to definitions using the `@` prefix syntax. Annotations provide
  compiler directives and metadata that affect how code is treated during
  compilation and evolution."
- `@deprecated` (610-663): "When code references a deprecated definition,
  the compiler produces a warning"; "Deprecated definitions can use other
  deprecated definitions without warnings"; its fields `Message` ("Passing
  `false` means 'no message' and is accepted") and
  `DiscontinuedAtFNVersion` ("the version at which use stops being a warning
  and becomes a hard error"); "`@deprecated` may also be applied to a
  module, in which case it covers the module's members"; it applies to
  "Functions and methods; Classes, interfaces, structs, and enums;
  Individual enum values; Data members; Modules".
- `@experimental` (670-703): "Experimental features can only be used when
  the `AllowExperimental` package flag is enabled"; "cannot be applied to:
  Local variables; Override methods".
- `@available` (707-736): "controls when a definition becomes available
  based on version numbers", `@available{MinUploadedAtFNVersion := 3000}`;
  "can be applied to the same kinds of definitions as `@deprecated`".
- Custom attributes (743-847): "You can create custom attributes by
  inheriting from the special `attribute` class"; the scopes
  `@attribscope_class`, `_attribclass`, `_enum`, `_interface`, `_function`,
  `_data`; "Attempting to use an attribute in the wrong location produces a
  compiler error"; "Custom attributes are currently metadata for external
  tooling — the compiler, LSP, and the Unreal Editor can read and act on
  them, but there is no Verse API to query attributes at runtime."

## The rules

### Syntax

An attribute is `@` and a name, perhaps dotted (`@a.bb`,
`2021-10-05-AttributeNames.versetest`), then its arguments in parentheses
right after it, `@test("…")`, or its fields in braces on its line,
`@deprecated{Message := "…"}`, `@available {MinUploadedAtFNVersion := 3800}`,
or both (`@attr(a:=1){b:=1}`, `TimSyntax.versetest:175`). A space, a new line
or another attribute follows it (`Attributes.versetest` 11-14, 28-31:
`@doc; X:int=4`, `@doc:foo X:int=4` and `X:int=@doc()4` are syntax errors,
`@doc@moc X:int=4` is not); comments may come between `@` and the name
(`Roundtrip/Comments.versetest:121`). Attributes are written before:

- a definition of a module or of the top level (on its line, or on lines of
  their own above it): a function, a constant, a class, an interface, a
  struct, an enum, a type alias, a module;
- a member of a class or an interface, a struct's field, an enum's value
  (`Enum.versetest:80`, `deprecated.versetest:30`);
- an expression, `(@ignore_unreachable return X+1)`, and a `case` arm,
  `@ignore_unreachable ClosedEnum.C => 9` (`Return.versetest:83`,
  `Enum.versetest:514`): the syntax allows any attribute there; only
  `@ignore_unreachable` is valid (`deprecated.versetest:83`, 3604;
  `experimental.versetest:35`, 3553).

Not on a parameter (`Function.versetest` 110-113, `deprecated.versetest`
88, 91: 3596) and not inside a type or after a name (`X@doc():int`,
`X:@doc()int`: syntax errors).

### The built-in attributes

| attribute | where | fields | meaning |
|---|---|---|---|
| `@deprecated` | functions, methods, classes, interfaces, structs, enums, enum values, data, modules, type aliases (`deprecated.versetest:435`) | `Message` (a string, or `false`, no message), `DiscontinuedAtFNVersion` (an int; needs a `Message` that is not empty, 3696); none else (3506), none twice (3532); `@deprecated(…)` is no attribute (3509, 3547) | a use from code that is not deprecated is warned of (2009); a module's members are deprecated with it; at or past `DiscontinuedAtFNVersion` a use is an error (3695), which needs a package's upload version |
| `@experimental` | as `@deprecated`, not on an override (3553) or a local (3553) | none | a use needs the package flag `AllowExperimental`, else 2304 |
| `@available` | as `@deprecated` | `MinUploadedAtFNVersion` (an int); `@available{}` "has no effect" (`available.versetest:50`) | a definition is in a package uploaded at that version or later, else out: its uses are unknown names (3506, `available.versetest:304`); a member of a definition versioned out is out with it |
| `@attribscope_class`, `_attribclass`, `_enum`, `_interface`, `_function`, `_data`; the tests add `_enumerator` (`Enum.versetest:76`) and `_name` (`Function.versetest:106`) | an attribute class | none | the places an attribute of that class may be written (3596 elsewhere): `_class` classes, attribute classes included (`CustomAttributes.versetest:24`); `_attribclass` attribute classes; `_function` functions and methods, an interface's included; `_data` data members; `_enumerator` enum values; `_name` a name's specifier `<attr>` |
| `@ignore_unreachable` | an expression, a case arm | none | the code it marks may be code never reached, with no warning or error (`Enum.versetest:505`, `Reachability.versetest:93`) |

The tests also write `@export_metadata`, `@expose_to_web_data_sync_service_reads`
and `_writes`, `@customattribhandler`, `@doc(…)`, `@test(…)` and `@import_as`;
the first two need the test runner's packages and the engine
(`export_metadata.versetest`, `WebDataSyncService.versetest`), the others are
in syntax tests only or defined by the test (`@test`, `Enum.versetest:78`).

### Custom attributes

An attribute class is a class below `attribute` (`gameplay_element :=
class<computes>(attribute)`); its scopes are the `@attribscope_…` written on
it, and an attribute of it is valid where one of them allows
(`CustomAttributes.versetest` 23-73, every pair of scope and place). An
attribute is `@c` (the class's value `c{}`), `@c{F := e}` (a value of it) or
`@f(…)`, a call of a constructor function of the class (`sol1729<constructor>(importName:string)<computes>
:= sol1729_attribute{}`, `SOL-1729…:8`; `test<constructor>(text:string)`,
`Enum.versetest:78`); `@c(…)` of a class is a cast, no attribute. Its
arguments are evaluated where the definition is, and see no instance
member (`CustomAttributes.versetest` 72-75: `@Attr{V:=Y}` with a field `Y`
is 3506, with `Self.Y` 3548). A name that is no attribute class, nor a
constructor of one, is no attribute (`Attributes.versetest` 4-7: `@int`,
`@c` of a plain class, `@F()` of a function, 3553; `@option`, 3502). An
attribute class and its constructors are named in attributes only: as a
class to construct, a constructor to call, a type or a value, it is an error
(`SOL-1729…` 16-52, 3670).

### At run time

Nothing: "there is no Verse API to query attributes at runtime" (ch. 12,
846). An attribute changes no value a program computes; `@available`
changes which definitions a program has.

## Error codes

| code | what |
|---|---|
| 3100, 3101 | the syntax (`Attributes.versetest` 11-14, 24-26, 34-38) |
| 3502 | `@option` (`Attributes.versetest:5`) |
| 3506 | `@deprecated{NotMessage := …}` (`deprecated.versetest:113`); a member read from an attribute (`CustomAttributes.versetest:74`); a use of a definition versioned out (`available.versetest:304`) |
| 3509, 3547 | a field of the wrong type (`deprecated.versetest:104`); `@deprecated(…)` (:128) |
| 3532 | a field given twice (`deprecated.versetest:123`) |
| 3548 | `Self` in an attribute (`CustomAttributes.versetest:75`) |
| 3553 | not an attribute (`Attributes.versetest` 4-7); `@experimental` on a local or an override (`experimental.versetest` 35, 54) |
| 3596 | an attribute where its scopes do not allow it, or on a parameter (`CustomAttributes.versetest`, `Function.versetest`, `deprecated.versetest` 88-91) |
| 3604 | an attribute on an expression (`deprecated.versetest:83`) |
| 3670 | an attribute class used as a class, a type or a value (`SOL-1729…`) |
| 3696 | `DiscontinuedAtFNVersion` with no `Message` (`deprecated.versetest:160`) |
| 2009 | a use of a deprecated definition (a warning) |
| 2304 | a use of an experimental definition without `AllowExperimental` (a warning code; `experimental.versetest:5`) |
| 3695 | a use of a definition discontinued at the package's version |

## Where the prose and the tests disagree

- **`@experimental`.** The prose: "Experimental features can only be used
  when the `AllowExperimental` package flag is enabled" (ch. 12, 671-672),
  which reads as an error. The tests: a use without the flag is
  `assert_semantic_error(2304)` (`experimental.versetest:5` and 8-47), a
  code of the Book compiler's warnings (2000-2999). openverse follows the
  tests where it can: it has no packages, so no flag, and reads the flag as
  set (below), where neither applies.

## Readings openverse takes

- **No packages, so no versions and no flags.** openverse's programs are in
  no package. `@available{MinUploadedAtFNVersion := N}` versions a
  definition in unless `N` is at least `4294967295`, the largest 32-bit
  version, which no upload reaches: the tests version `0` and `3000` in
  outside a package (`available.versetest` 6-62, 326) and `4294967295` out
  (:304). `@experimental` is metadata: a program is read as one whose
  package allows experimental definitions (as `?AllowExperimental:=true`,
  `experimental.versetest:4`). `DiscontinuedAtFNVersion` is checked but
  never reached, as no package has an upload version.
- **Deprecation warnings.** openverse finds the uses of deprecated
  definitions (`Attributes.deprecations`); they are reported once the
  compiler has a channel for warnings (the readings audit's), until then
  they are found and not shown, and the 23 Book cases that expect 2009 are
  counted as accepted refusals.
- **A use through overloads.** A name that is also an overload that is not
  deprecated is not judged before the elaboration picks one
  (`deprecated.versetest:413`).

## Design

- **The parser** reads `@` (a symbol of its own) and keeps an attribute
  among the specifiers of its definition's name, `@name` beside `<public>`,
  and as a record after the definition, `$attr:L_C`, whose specifiers are
  the definition's place, name and position and whose value is the
  attribute as written; a member's are given out after its class. On an
  expression, `@ignore_unreachable e` is `e`, a marked `case` arm is
  recorded by position (`TyEnv.ignoredArms`), and any other attribute wraps
  the expression in `$attributes`.
- **`Attributes.apply`**, the first step of `elabProgram`, reads the
  records and checks each attribute (the rules above), removes the records
  and the `@name` specifiers, refuses `$attributes`, takes out the
  definitions `@available` versions out, adds the class `attribute`
  (`<abstract><computes>`) when the program has classes below it, and adds
  for each custom attribute a constant `$attrCheck:N@a` of its class whose
  value is the attribute's: the elaborator checks it at that type, as it
  checks a function type's default (`checkTypeDefaults`), in the scope of
  the definition, and drops it, so no attribute is evaluated or compiled.
- **Nothing reaches Verse Core**: attribute classes are ordinary classes, no
  value of which is ever made.
