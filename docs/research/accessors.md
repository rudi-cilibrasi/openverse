# Fields with accessors

The rules openverse takes for a field with accessors,
`var X<getter(G)><setter(S)>:t = external{}`: what a getter and a setter
are, what a read and a `set` of such a field mean, with `var`, in classes and
interfaces, with overrides and access specifiers, and what is an error; then
what openverse builds. [LANGUAGE.md](../LANGUAGE.md#classes) states the rules
for users; [DESIGN.md](../DESIGN.md#fields-with-accessors-calls-of-their-classs-methods)
says how they are built.

## Sources

- The [Book of Verse at `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs):
  ch. 10, "Fields with Accessors" (`docs/10_classes_interfaces.md`
  3269-3311); ch. 12, "Getter and Setter Accessors" (`docs/12_access.md`
  849-883).
- Its tests: `Attributes/CustomClassVarAccessors.versetest`,
  `Attributes/DeepMutabilityForCustomClassVarAccessors.versetest`,
  `InterfaceWithAccessors.versetest`, `InterfaceWithFields.versetest`
  (428-505), `LengthOptimizationSafety.versetest` (38-72),
  `Attributes/CustomAttributes.versetest:76`,
  `Bugs/FORT-889314-InterfaceFieldOverriddenWithGetterSetterBroken.versetest`,
  `Bugs/FORT-976754-GetterSetter.versetest`.

No Epic compiler was run and no Epic source code was read.

## Quotations

- Ch. 10, 3271-3272: "Interfaces can define fields with custom getter and
  setter logic, encapsulating complex behavior behind simple field access
  syntax"; 3304-3305: "The `external{}` keyword indicates the field has no
  direct storage—all access goes through the accessor methods"; 3309-3311:
  "a field with accessors declared in an interface cannot be overridden in
  an implementing class. The accessor implementation is fixed by the
  interface."
- Ch. 12, 852: "Getter and setter accessors are currently an internal feature
  and cannot be used by end-users"; 856-857: "These can be applied to both
  class and interface fields"; 874-881, the constraints: "Must include both
  `<getter(...)>` and `<setter(...)>` - cannot have only one", "The field
  must have `= external{}` or no default value (with archetype initialization
  required)", "Fields with accessors cannot be overridden in subclasses",
  "The field must be mutable (marked with `var`)", "Not all types are
  supported for accessor fields", "Accessor fields are currently only allowed
  in epic_internal scopes".

## The rules

### Declaring

- **The field.** `var X<getter(G)><setter(S)>:t = external{}`, or with no
  default, in a class or an interface: one `<getter(…)>` and one
  `<setter(…)>` (`CustomClassVarAccessors.versetest:27`, 3553), naming bare
  identifiers (:111, 3687), on a `var` (:60, 3553); the default `external{}`
  or none (:43, 3600), and with none every construction gives it (:50,
  3600). A tuple type is refused (:88, 3502: "Not all types are supported").
- **The accessors.** `G` and `S` are methods of the class or interface or of
  one above it (:103, 3688: functions are refused), an interface's abstract
  ones implemented above the class that declares the field included (:475-491).
  Each takes first an unnamed parameter of the type `accessor`: the getter
  `G(:accessor):t` and the setter `S(:accessor, :t):void` at the field's type
  exactly, neither a subtype nor a supertype (:67, :699, :707, 3671). Their
  other overloads take a path after the accessor (below). Their effects are
  their own (`<transacts>` in the tests; `InterfaceWithFields.versetest`
  428-505 writes none).

### Using

- **A read** `O.X`, and `X` in a method of the class, is `O.G(accessor)`
  (:193-213); its value is the getter's.
- **A set** `set O.X = v` is `O.S(accessor, v)`, `O` evaluated first, then
  `v`, then the setter (:365-367, "BCS"); its value is `v` (:314-318).
  `set O.X op= v` reads the old value with the getter and sets the new one
  with the setter (`DeepMutability….versetest:338-344`).
- **A path** into the field's value, up to the first object in it, is one
  call of the overload that takes, after the accessor, the path's indices
  and the names of the struct fields it goes through, as strings, and for a
  setter the value (`DeepMutability….versetest:264-308`: `T.AF[0]` is
  `GetAF(accessor, 0)`, `set T.AS[0].AI[0] = 666` is
  `SetAS(accessor, 0, "AI", 0, 666)`; :365-375, `set T.C.X.Z = 3.3` calls
  `SetC(:accessor, :[]char, :[]char, :float)` and no other). A path that
  goes on into an object reads the field with the getter and goes on in the
  object (:319-325: `set T.C.I = 888` is `GetC1`, then `SetI1`). A step that
  is no index or struct field ends the path: `A.Items.Length` reads the field
  (`LengthOptimizationSafety.versetest:38-50`).
- **A construction** `C{X := v}` calls the setter with `v` once the object's
  fields have their values (:586, the setter sees the other fields set) and
  before its `block:` clauses (:661-681: `set X = 10` in a `block:` is what
  stays).
- **A failure context** undoes what the accessors wrote, as any other write
  (the tests' `if (set R.X = 45; 1 = 2)`).

### Inheriting and overriding

- A field with accessors is inherited with them (:249-266, :423-431), and is
  read through any class or interface above the object's.
- It is not overridden, by a field with storage or with accessors (:11-17,
  `InterfaceWithAccessors.versetest` 43-71, 3523), and its accessors are not
  overridden below the class or interface that declares it (:19-24,
  `InterfaceWithAccessors.versetest` 73-85, 3523).
- A class may give a field with storage of a class or interface above it
  accessors, `var X<override><getter(G)><setter(S)>:t = external{}`
  (`InterfaceWithAccessors.versetest` 24-40), and its objects are then read
  and set through them also through the type above
  (`LengthOptimizationSafety.versetest` 52-72: "Access via the subclass and
  via the interface both reach the same accessor at runtime").

### Access

A use is judged by the field's access, and a `set` by its `var`'s; the
accessors' own access is not (`<private>` accessors of a `<public>` field,
`FORT-976754-GetterSetter.versetest:23-41`; `GetP<private>` of
`var P<private>`, :172-179). Nothing else can call an accessor: no program
makes a value of `accessor`.

## Readings openverse takes

- **No scopes.** "Accessor fields are currently only allowed in epic_internal
  scopes" (ch. 12; :79, 3593 in a `PublicAPI` package): openverse has no
  packages or scopes, so it allows them wherever a field is.
- **Order of a construction's values.** openverse evaluates a construction's
  field values in the order the fields are declared (LANGUAGE.md, Classes);
  the values of fields with accessors take their places among them. (The
  Book's tests of the order, :393-418, use `CoroUtils` and blocks inside an
  archetype, which openverse does not translate.)
- **A path with no overload** for it is refused; the tests always give one.
- **The accessor's type** is `accessor` only as an accessor's first
  parameter; a program that defines its own `accessor` keeps it.

## Not built, and why

- A constructor function (`K<constructor>() := c: X := v`) that gives a field
  with accessors: refused as a field the class does not have; its lowering,
  `K$init`, gives the stored fields as a struct.
- A path into the field's value through a type above a class that gives a
  field with storage accessors: refused (the read or set of the field itself
  is built).
- A field with storage given accessors in a class with type parameters, used
  through a type above it: refused.
- Two interfaces' fields with accessors of one name in one class,
  `Object.(Interface80:)Value` (`InterfaceWithFields.versetest:463`): the
  class inherits each interface's accessor `GetValue`, which openverse
  refuses without an override (#70), and an override of an accessor is an
  error.

## Where the prose and the tests disagree

Nowhere for accessors themselves. The prose's "Fields with accessors cannot
be overridden in subclasses" (ch. 12, 878) is about the field with
accessors; the tests' override of a field with storage by one with accessors
(`InterfaceWithAccessors.versetest` 24-40) is a different case, which both
allow.
