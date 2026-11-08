# The Verse subset of openverse v1

openverse implements a deterministic, single-threaded core of Verse as
described by the [Book of Verse](https://verselang.github.io/book/) (Epic
Games; the book tracks the head of Verse's development branch). The digest in
[`research/book-of-verse-digest.md`](research/book-of-verse-digest.md) quotes
the book for every rule used here. Where the book is silent or contradicts
itself, this page says which reading openverse takes.

The meaning of the subset is fixed by the Lean definitions, not by this page:
surface Verse is elaborated (`OpenVerse/Front/Elab.lean`) into Verse Core
(`OpenVerse/Core/Syntax.lean`), whose semantics is the big-step relation of
`OpenVerse/Core/Semantics.lean`.

**Contents**

- The language: [Supported](#supported) · [Source text](#source-text) · [Parametric functions](#parametric-functions) · [defer](#defer) · [Overloading](#overloading) · [Parametric structs](#parametric-structs) · [Classes](#classes) · [Mutation, macros, tooling](#mutation-macros-tooling)
- More types: [any](#any) · [Refinement types](#refinement-types) · [float](#float) · [rational](#rational) · [char32](#char32)
- Programs: [Modules](#modules) · [Programs of several files](#programs-of-several-files) · [Concurrency](#concurrency)
- [Readings openverse takes](#readings-openverse-takes) · [Not supported in v1](#not-supported-in-v1)

## Supported

| Area | Supported | Book |
|---|---|---|
| Comments | `#` to the end of the line, nested `<# … #>`, `<#>` indented comments (the rest of the line and every following line indented more than it; see [Source text](#source-text)) | ch. 0 |
| Literals | `int` (decimal, `0x` hex; must fit in 64 bits), `'c'` `char` (`c` printable ASCII U+0020–U+007E, or an escape), `0oHH` `char` code unit (one or two hex digits, not octal: `0o41` is `'A'`, `0o9` is a tab), strings with escapes and `{expr}` interpolation, `true`, `false`, `0uHHHHHH` `char32` (a Unicode scalar value, up to `0u10FFFF`, no surrogates), `float` `1.5`, `2.0e-7`, `1e3` (digits, then a point and digits or an exponent or both; the nearest double) | §1.3–1.7 |
| Types | `int`, `logic`, `char`, `char32`, `any` (see [any](#any)), `rational` (see [rational](#rational)), `float` (see [float](#float)), refinement types `type{_X:int where 0 <= _X, _X <= 120}` (see [Refinement types](#refinement-types)), `string` (= `[]char`), `[]t`, `?t`, `tuple(…)`, `void`; a tuple converts to an array of its elements where an array is expected, and compares with an array as one (`array{1,2} = (1,2)`) | ch. 2–3 |
| Definitions | top-level functions `F(X:t, …)<effects>:t = body`, top-level constants `C:t = e` / `C := e`; locals `X := e`, `X:t = e`, `var X:t = e`; no shadowing | §3.1–3.4 |
| Mutation | `set X = e`, `set X += e` (`-=`, `*=`), `set A[i] = e` (fails out of range; returns `e`), and paths `set S.F.G = e`, `set A[i][j] op= e`, `set M[k].F = e`: indices and keys evaluated once, left to right, then the new value (for `op=`, after the old one is read: `set X += e` is `set X = X + e`), then the variable rebuilt; an index out of range or a missing intermediate key fails, while the last key of a path inserts | §3.3, §3.5, §9.3 |
| Blocks | indented (`:`), braced (`{ }`), inline (`then`/`do`), `block:`, `( a; b )` sequences | §2.2–2.4 |
| Operators | `* + -`, unary `-`, comparisons `= <> < <= > >=` (failable, return the left operand, chains check every pair), `and`, `or`, `not` (below the comparisons, above `and`: `not X = Y` is `not (X = Y)`), `?`, `.Length`, `A[i]`, `T(k)` | ch. 4 |
| Failure | failure contexts (`if` conditions, `for` clauses, `option{}`, `logic{}`, `not`, left of `or`, `<decides>` bodies) with rollback of `var` writes **and output** | ch. 8 |
| Control | `if`/`else if`/`else` (all styles, `if:`…`then:`), `for` with `X : array`, `I -> X : array`, `X := a..b`, filters, bindings, several generators (cartesian product), `loop`/`break`, `return`, `case` with literal patterns and `_` | ch. 7 |
| Functions | a tuple argument expands into several parameters (`Describe(MyTuple)`), several arguments make a single array parameter (`Sum(1, 2, 3)`) (#134, #140; the array form for a plain call only, and a method's, an overloaded or a generic function's tuple is typed without the parameters' types); recursion, mutual recursion, `<decides>` (called with `F[…]`; other functions with `F(…)`), named parameters `?P:t = default` passed as `?P := e` (positional, then named as written, then defaults; a default may use the parameters before it, and a method's default the method's fields; a default is evaluated at the call, its effects counting as the caller's, and cannot return, break or use itself), the heap effects `<computes>`, `<reads>`, `<writes>`, `<allocates>`, `<transacts>` (checked, see [Classes](#classes)), other effect specifiers accepted and ignored | ch. 6, 13 |
| Parametric functions | `F(X:t, … where t:type, u:subtype(comparable))`: type parameters in parameter types, the result type and local declarations; type arguments inferred at each call (see [Parametric functions](#parametric-functions)) | Types: where clauses |
| Structs | `name := struct:` with typed fields and defaults, `name{F := e, …}`, `S.F`, `set S.F = e` / `op=`, structural equality (a struct is the tuple of its fields in Verse Core) | ch. 9 |
| Parametric structs | `pair(t:type, u:type) := struct:`, the type `pair(int, string)`, values `pair(int, string){First := 1, Second := "a"}` (or `pair{…}` where the expected type gives the type arguments); see [Parametric structs](#parametric-structs) | ch. 9 |
| Classes | `name := class:` and `name(t:type) := class:` with fields and methods; `class(parent, interface, …)`, `interface`, `<abstract>`, `<override>`, `<final>`, `(super:)`, virtual dispatch, casts `T[X]` and `T(X)`; no `var` fields; see [Classes](#classes) | ch. 10 |
| Enums | `name := enum:` / `enum{A, B}`, `name.A`, equality, `case` that needs no `_` when every value is named (an enumerator is its index in Verse Core); `enum<open>` may gain values, so a `case` on one needs `_` or a failure context (`<closed>` is the default) | ch. 9 |
| Maps | `[k]v`, `map{k => v, …}` (a key given twice keeps its last value, at its last position), `M[k]` (fails on a missing key), `set M[k] = v` (insert or update, never fails), `set M[k] op= v` (fails on a missing key), `.Length`, `for (V : M)`, `for (K -> V : M)` in insertion order, `ConcatenateMaps(M1, M2, …)` (a later map's value wins for a key, which keeps its first position), order-sensitive equality (a map is the array of its pairs in Verse Core) | §3, §9.3 |
| Array methods | `A.Slice[i, j]`, `A.Slice[i]`, `A.Find[x]`, `A.RemoveElement[i]`, `A.RemoveFirstElement[x]`, `A.Remove[i, j]` (half-open), `A.ReplaceElement[i, x]`, `A.ReplaceFirstElement[x, y]`, `A.Insert[i, B]`, `A.Last[]`, `A.Last[n]` (the element n before the last) (all failable); `A.RemoveAllElements(x)`, `A.ReplaceAllElements(x, y)`, `A.ReplaceAll(Pattern, Replacement)` (contiguous subarrays, left to right, not overlapping; an empty pattern changes nothing), `Concatenate(A, B, …)` or `Concatenate(Arrays)` (#150) (never failing) | §9.1 |
| Built-ins | `Print(s)`, `ToString(x)` (int, float, char, string), `Floor[F]`, `Ceil[F]`, `Round[F]`, `Int[F]` (of a float, failable), `Floor(R)`, `Ceil(R)` (of a rational or an int, never failing; `Floor(X / Y)` fails when `Y = 0`, as `X / Y` does), `Quotient[X, Y]`, `Mod[X, Y]` (Euclidean), `Abs`, `Min`, `Max`, `Err()` | API reference |
| Modules | `name := module:` (nested), `M.F`, `A.B.F`, the types `M.c` and values `M.c{…}`, `(M:)F`, `using{M}` at file or module scope, `<public>` members (`<internal>` is the default); see [Modules](#modules) | ch. 16 |
| Concurrency | `<suspends>` functions and methods, `Sleep`, `sync`, `race`, `rush`, `branch`, `spawn` with `task(t)` and `Await`, `event(t)` with `Signal` and `Await`, cancellation with `defer:`, under a deterministic scheduler; see [Concurrency](#concurrency) | ch. 14 |
| Program entry | `Main()` — see the exit protocol in [`FORMAT.md`](FORMAT.md) | (not in the book) |

## Source text

openverse follows Verse's lexical grammar for the characters of a file:

- A source file is UTF-8. Malformed UTF-8 is an error at the line and column
  of the first bad byte. A byte order mark (U+FEFF) as the very first
  character is skipped.
- These characters are rejected anywhere, including inside strings, char
  literals and comments: the C0 controls U+0000–U+001F other than tab, LF and
  CR; DEL (U+007F); the C1 controls U+0080–U+009F; U+2028 and U+2029.
- LF, CR LF and a lone CR are each exactly one line break: for line and
  column numbers, for the end of a `#` comment, and for string literals,
  which cannot contain one.
- Error positions are `line:column`, lines from 1 and columns from 0.
  Columns count characters, so a tab is one column.
- `<#>` starts an indented comment: the rest of its line, then every
  following line indented more than the line that contains the `<#>` (more
  leading tabs and spaces, counted as columns like the offside rule does),
  with blank lines inside included. It ends before the first non-blank line
  indented no more than that line. `<#` opens a nested block comment only
  when the next character is not `>`; inside a block comment, `<#>` opens
  nothing, so its `#>` closes the block comment.
- A `0o` char literal is `0o` and one or two hex digits, not followed by a
  letter, digit or `_`; anything else (`0o`, `0o123`, `0o4g`) is an error.
  Its value is that UTF-8 code unit, so `0oC3` is a valid `char` although it
  is not ASCII.

**Indentation.** The indentation of a line is its leading string of tabs and
spaces. The offside rule compares columns, and a tab is one column, so to
keep the meaning of a program independent of the width of a tab, each line's
indentation must be consistent with that of the innermost enclosing indented
block: one must be a prefix of the other. Otherwise the line is rejected
("inconsistent use of tabs and spaces"). The indentation of a block is that
of the line of its first token, the one whose column the block uses. A line
that ends a block is also checked against the block it ends, and the first
line of a block against the enclosing block. Blank lines and comment-only
lines are exempt. Indented blocks are those after `:` (and a function's
`=`), the `:` forms of `case`, `struct` and `enum`, and braced blocks and
`case {…}` whose first element starts a line; lines inside parentheses,
brackets, or a braced block that starts on the line of its `{`, are checked
against the enclosing indented block.

## Parametric functions

A function with a `where` clause is generic. The clause ends the parameter
list and declares each type parameter as `t:type` or
`t:subtype(comparable)`:

```verse
Find(Items:[]t, Target:t where t:subtype(comparable))<decides>:int = ...
Combine(A:t1, B:t2 where t1:type, t2:type):tuple(t1, t2) = (A, B)
```

- **Checked once.** The body is type-checked once, with every type parameter
  opaque. A value of type `t` can be bound, passed, returned, stored in
  arrays, options, tuples and maps, and iterated over in a `[]t`. `=`, `<>`,
  `Find` and map keys need `t:subtype(comparable)`. Anything else, such as
  arithmetic, `ToString` or `.Length` on a bare `t`, is a type error, even if
  the function is never called.
- **Inferred type arguments.** At a call, the result type is matched against
  the expected type (unless that is `void`), then each parameter type against
  its argument's type. Arguments are matched left to right, except that
  `false`, `array{}` and `map{}` are matched last, because they take their type
  from context. A type parameter that is still unknown is an error. Arguments
  are still evaluated left to right.
- **Compiled once.** A generic function is one Verse Core function, whose
  types mention type variables, checked once by `Prog.checkTypes` for every
  instantiation (the substitution lemma `Typed.subst`). It takes one hidden
  argument per type parameter, a value of that type, which initialises its
  slots of that type (see [`DESIGN.md`](DESIGN.md)). So every call runs
  exactly the code that was checked, and it behaves the same way at every
  type argument. Polymorphic recursion, where a function calls itself at a
  larger type, is allowed.
- **Named parameters** (#119) work as for other functions: positional
  arguments, then named ones as written, then the defaults of those
  omitted. The type arguments are inferred from every argument given. A
  default has its parameter's type at them, and may itself determine a type
  parameter nothing else does (`Pick(A:t, ?Other:t = A where t:type):t`).
- **Limits.** A generic `Main`, several constraints on one type parameter
  (also unsupported in the Book), explicit type arguments to a generic
  function, and generic constants are not supported.

## defer

`defer:` followed by a block runs that block when its scope exits (Book of
Verse ch. 7): at the scope's end, after its value is computed, or on a
`return` or `break` that leaves it. Several run last registered first. A
scope that fails runs none, since its effects are rolled back. A `defer:`
block cannot be empty, fail, `return`, or `break` out of itself, and it is a
statement, not a value. Lowering: the deferred block is placed after the
rest of its scope, and before each `return` (after its value) and `break`
that leaves it.

## Overloading

Several functions may share a name when no call could fit two of them (Book of
Verse ch. 6): `Describe(X:int)`, `Describe(S:string)`, `Describe(X:int, Y:int)`.
- **Distinct overloads.** Overloads take different numbers of parameters, or
  disjoint types at some position. A single tuple parameter counts as many
  parameters as its elements.
- **Overlapping types:** `void`, a type parameter, two array, map or option
  types (they share the empty one), an array, option or `logic` with
  another (`false` is each), a tuple and an array, map or option, and a
  class or interface with an interface or a class above or below it (but a
  `<final>` class and an interface it does not implement are disjoint, and
  so are one parametric class's instances at disjoint type arguments). A pair that overlaps is refused where the later
  one is defined.
- **Calls.** A call takes the overload whose parameter types its arguments
  fit. With subtyping, a `square` fits `Describe(B:shape)`. Each argument's
  own type is found once, and the arguments are elaborated at a
  candidate's parameter types only when that leaves several, so nested
  overloaded calls stay cheap. An overloaded name is not a value.
- **Lowering.** Each overload is a separate function (`F$ov0`, `F$ov1`, …).
- **Named parameters.** Overloads may have named parameters. A call fits an
  overload when it gives as many positional arguments, names only
  parameters the overload has, and gives every one it requires. The order
  of named parameters and their defaults do not tell overloads apart, so
  two overloads are distinct only if their positional parameters are, or
  some named parameter one requires is missing from the other or has a
  disjoint type there.
- **Generic overloads.** A type parameter overlaps every type, so a generic
  overload is told apart from the others by its number of parameters, or
  by a type its pattern cannot take (`?t` against `int`). A call matches
  the arguments' types against its patterns as inference does, and infers
  its type arguments as for any generic call. (Generic functions take no
  named parameters.)
- **Methods.** A class or interface may declare a method with several
  parameter lists, and a subclass may override one overload (with its
  list) and add others. A call takes the overload visible at the
  receiver's type that its arguments fit, then dispatches as usual; the
  overloads a class sees must be distinct. Each list is a method of its
  own (`M$ovN`, up to the names of type parameters).
- **Qualified implementations** (#125). `(i:)M<override>(…)` implements
  the overload of `i`'s `M` with its parameter list (as an override takes
  its method's), and `X.(i:)M(…)` picks among `i`'s overloads.
- **Not yet supported:** overloading `Main`.

## Parametric structs

A struct with parameters is a family of struct types:

```verse
pair(t:type, u:type) := struct:
    First:t
    Second:u

Swap(P:pair(t, u) where t:type, u:type):pair(u, t) =
    pair(u, t){First := P.Second, Second := P.First}
```

- A parameter is `t:type` or `t:subtype(comparable)`. The field types and
  field defaults may use it.
- `pair(int, string)` is a type. A parametric struct used without type
  arguments, or with the wrong number of them, is an error, and so is a
  non-parametric struct used with type arguments.
- A value is written `pair(int, string){…}`, or `pair{…}` where the expected
  type supplies the type arguments, as in `R:pair(string, int) = pair{…}`.
  Type arguments are not inferred from the fields.
- Each field default is type-checked once, at its definition, with the
  parameters opaque (`Value:t = 0` is an error). It is elaborated again, at
  the field's type, wherever a construction omits the field. That second
  elaboration can still fail in one corner case: a default that calls a
  generic function whose type parameter is inferred only from the expected
  type, at a `void` type argument. A default that depends on itself, directly
  or through another struct's default, is an error.
- A type whose Verse Core representation would exceed 100000 nodes is
  rejected. A struct with two fields of its parameter doubles in size at each
  level of nesting.
- In Verse Core a struct is the tuple of its fields, so `pair(int, string)`
  is a `tuple(int, []char)`. Two instantiations are the same type when their
  type arguments are, and struct equality is by value.
- A struct that contains itself, directly or through a type argument (as in
  `b := struct: Y:?wrapper(b)`), has no finite representation and is
  rejected.
- An instantiation counts as comparable when all its type arguments are
  comparable.

## Classes

Classes (#14, #18, #34): fields and methods, `var` fields, `<unique>`
classes, recursive classes, parametric classes, single inheritance,
interfaces and virtual dispatch.

```verse
shape := class<abstract>:
    Name:string = "shape"
    Area():int
    Describe():string = "{Name} of area {Area()}"

circle := class(shape, labelled):
    Name<override>:string = "circle"
    R:int
    Area<override>():int = 3 * R * R
    Label<override>():string = "a circle"
    Describe<override>():string = "round: {(super:)Describe()}"
```

- **References.** An instance is an object, constructed like a struct
  (`circle{R := 1}`). A class value is a reference to it, so every alias sees
  the object's `var` fields change.
  - `var F:t = e` declares a field that `set` can change: `set C.F = e`,
    also through a path (`set H.C.F = e`, `set Cs[i].F = e`) and through any
    variable, `var` or not, because the reference does not change. The
    object is written in place; the containers on the path above it are not
    rebuilt. Other fields cannot be set. In a method, `set F = e` sets a
    field of `Self`.
  - A failure context undoes the field writes and the constructions it made
    (`if (set C.N = 1, Fails[]) …`), as for variables.
  - A class may hold itself, through an option or an array
    (`node := class: var Next:?node = false`). A class that *requires* an
    instance of itself can never be constructed, but its variables are
    fine (they are only reached by code that never runs).
  - Every variable of a class type starts as a *prototype* until it is set,
    which Verse code always does before reading it: one object per class,
    made once before `Main` with default field values (#37), so it costs
    nothing per call. Prototypes may refer to each other, so even classes
    that require instances of each other have them.
  - A `set` path that reaches an object evaluates the right-hand side once
    it has reached the object, and then reads the values inside it, so that
    a write the right-hand side makes through the object is kept
    (`set O.P.X = O.SetY()`). A path without an object reads every
    container first, as `set A[i] = e` does.
  - A class or interface with no concrete class below it has no instance,
    so code that uses a value of its type is unreachable, and accepted.
- **Methods.** A method `M` of class `c` is a function `c.M` whose first
  parameter is `Self`. In its body, a name that is not a local is looked up
  among the fields, then the methods, inherited ones included. A local or
  parameter with the name of a field or method is an error, and so is a
  method named like a built-in function. Field defaults are elaborated where
  they are defined. `Obj.M(…)` evaluates `Obj` before the arguments.
- **Inheritance.** `c := class(parent, i₁, …)` has at most one class parent
  and any number of interfaces, and `i := interface(j, …)` extends
  interfaces. Interfaces may declare fields, with or without defaults. A
  class inherits its parent's fields, then those of the interfaces above it
  that are not there yet (once, along a diamond), then its own, and its
  methods:
  - `Name<override>:t = e` gives an inherited field a new default; any
    other field with an inherited name is an error;
  - `M<override>(…)` overrides an inherited method with its signature, except
    that it may return a class below the declared one (covariant results).
    Overriding without `<override>`, or `<override>` that overrides nothing,
    is an error;
  - `<final>` methods cannot be overridden, and `<final>` classes cannot be
    inherited from;
  - `(super:)M(…)` calls the implementation inherited from above.
- **Abstract.** An `<abstract>` class, or an interface, may declare methods
  without a body and cannot be constructed. A concrete class must implement
  every method it has, and must override a method that two unrelated
  interfaces both provide.
- **Subtyping and dispatch.**
  - A value of a class can be used wherever a class or interface above it is
    expected, and so can arrays and options of them.
  - Two `if` branches of different classes take the expected type when both
    are below it, else their nearest common supertype.
  - A method call runs the most specific implementation for the value's own
    class: the nearest in its class chain, else the most specific interface
    default, whatever order the parents are listed in. This is virtual
    dispatch, also inside a method; `(super:)` uses the same rule.
  - An implementation must have the signature of every declaration it
    satisfies.
- **Constructor functions** (Book of Verse ch. 10). A constructor is written
  `MakeP<constructor>(N:string)<effects> := player:` followed by indented
  items, and called as `MakeP("a")`, or `MakeP["a"]` when `<decides>`.
  - **Items** run in order: an indented block, items on the same line
    separated by `;`, or `{…}`. `F := e` sets a field of the class, `e`
    elaborated at the field's type. `let:` gives declarations later items
    see. A `block:` runs, and can neither fail nor `return`.
    `D<constructor>(args)` delegates to a constructor of the class (which
    then sets all fields) or of a class above it (which sets its fields;
    the class's own fields are set before it). A constructor of an
    `<abstract>` class can only be delegated to.
  - **Construction.** Fields not set take their defaults, and a field
    without one must be set. The class's own `block:` clauses then run, as
    for `player{…}`. A constructor sees no `Self`.
  - **Parametric classes.** The archetype names the class's type
    arguments: `MakeBox<constructor>(V:t where t:type) := box(t):` is a
    generic constructor, and `:= box(int):` a fixed one. Delegating to a
    generic constructor instantiates it. As for generic functions, its type
    parameters must appear in its parameters, and it takes no named ones.
  - **Overloads.** Constructors of one name construct one class (at the
    same type arguments) and take parameters no call fits two of, as
    overloaded functions do. A call or a delegation, even to another
    overload of the name, takes the one its arguments fit.
    - *Fields.* Each overload sets the fields it names. An overload that
      leaves a field to another gives it its default, evaluated when its
      items run (outside its parameters' scope).
    - *Delegation.* A constructor that delegates to an overloaded name
      cannot set a field that any overload of that name sets.
    - *Cycles.* A delegation cycle through overloads is decided at run time,
      as recursion is.
  - **Lowering.** `K` becomes `K$init`, which runs the items and gives the
    fields as a struct, and `K`, which constructs the class from them. A
    delegation calls the delegate's `$init`. For a generic constructor both
    are generic, and the struct is parametric over its type parameters.
- **Qualified implementations.** A class that implements two interfaces
  declaring the same method can give each its own: `(i1:)M<override>()`
  and `(i2:)M<override>()`. Each declaration that overrides nothing (a
  *root*) is a separate slot. The qualifier names the root: the interface,
  or class, that introduces `M`.
  - **Choosing.** For an object, a slot's implementation is the most
    specific `(r:)M` or plain `M` above its class that is below `r` or
    reached through a class of its chain that is not below `r`. As in Java,
    what a class has (its own method, or a default it inherits) implements an
    interface that a subclass adds. A default of the class's own interfaces
    implements only the slots above it.
  - **Calls.** A call through an `i1` uses slot `i1`. `X.(i1:)M()` names it,
    and inside a method a bare `(i1:)M()` is `Self.(i1:)M()`. A call through
    a type whose slots some class below implements differently is refused as
    ambiguous, so every static path to a slot reaches the same code.
  - **`(super:)M()`** in `(r:)M` is slot `r`'s implementation above. In a
    plain `M` it is refused when the slots above differ.
  - **Restrictions.** A class gives `M` plainly or qualified, not both. A
    plain `M<override>` in a subclass implements all its slots.
- **Casts.** `T[X]` is `X` as a `T`, failing unless `X`'s class is below
  `T`. `T(X)` converts to a supertype and cannot fail.
- **Parametric classes.** A parametric class is a reference like any other
  (#39): `stack(t)` can have `var` fields, be `<unique>`, and refer to
  itself (`node(t) := class: Value:t; var Next:?node(t) = false`). It can be
  in a hierarchy: a subclass gives its parent type arguments, from its own
  type parameters (`square(t) := class(shape(t))`, in any order:
  `swap(a, b) := class(pair(b, a))`), fixed ones
  (`intcell := class(cell(int))`), and it may have type parameters of its
  own (`named(t, n) := class(cell(t))`). A class overrides a method if
  its type arguments are those of the class that declares it, up to
  renaming, except that it may fix some of them to closed types (#142):
  `int_box := class(box(int))` overrides `box(t)`'s `Get():t` with
  `Get():int`, and code generic over `box(t)` (or over an interface
  `box` implements) runs it, typed under `t = int`; the dispatch skips
  the classes whose fixed arguments the receiver's type rules out. One
  that repeats type arguments (`dup(t) := class(pair(t, t))`), fixes them
  to types that mention type parameters, or has more type arguments than
  the declaring class (type parameters of its own, or of a class between
  them) cannot override yet: code generic over the declaring class could
  not call it. An interface can be parametric too (#53):
  `container(t) := interface: Get():t`, with `box(t) := class(container(t))`.
  A class gives the interfaces above it exactly its own Verse Core type
  arguments (`box(t)` gives `container` `t`; a class implementing
  `container(t)` and `sink(u)` cannot), so code generic over `container(t)`
  dispatches to `box(t)`'s methods and casts `container(t)` to `box(t)`.
  An interface's fields are typed as it gives them: a class that fixes or
  repeats its type arguments (`intbox := class(holder(int))`) can still
  implement an interface whose members it does not override. Code generic
  over the interface reads and writes a field that sits at different
  places in its classes also when a class fixes its type arguments (to
  closed types), under the refinement those give (#157); a class that
  repeats them makes such a field unreadable there. An interface
  that extends a parametric interface gives it its own type parameters. Inherited field defaults see their
  own class's type parameters. A cast `square[S]` takes its type arguments
  from `S`'s, and is refused when it would need more. A method
  of a parametric class is generic over the class's type parameters, then
  its own. The type arguments come from the receiver, and the body is
  checked once in Verse Core (see
  [Parametric functions](#parametric-functions)).
- **Heap effects** (#35). A
  function's specifiers allow a set of heap effects: all of them when it has
  none or `<transacts>`, none with `<computes>`, and those named by
  `<reads>`, `<writes>` and `<allocates>`. Reading a `var` field *reads*,
  setting one *writes* (`set C.F op= e`, and a path that goes on past a
  `var` field, such as `set O.Arr[0] = e`, also *read* it), and
  constructing an object of a class with a `var` field or a `<unique>` one
  *allocates*; a call has its callee's declared effects (a call dispatched
  on the receiver's class, those of every implementation it may run), and
  a constant those of its initialiser: a constant takes no effect
  specifier. Field and argument defaults count where they are used. A
  body with an effect its function does not allow is an error, and so is
  an override that allows more than what it overrides, and a field that
  is a `var` through one parent and not through another. Variables and values are not the heap:
  `var` locals and immutable classes have no effect. Lean proves that a
  function without `writes` keeps every existing object as it was
  (`Prog.accepted_no_writes`). A constant cannot hold an object with `var`
  fields or of a `<unique>` class, since it is computed at each use.
- **`block:`.** A class's `block:` clauses run when an instance is
  constructed, after its fields are given, those of the classes above it
  first, each class's in order; they see the fields by name, as a method
  does, and their effects are those of their code (a parametric class's
  too). Interfaces have none.
- **`<unique>`.** A `<unique>` class (and every class below it) is
  comparable: `=` and `<>` test identity, so two instances with equal
  fields differ, and an alias equals its original.
- **Comparability.** Other classes and interfaces are not comparable (Book §4.9), nor
  is a struct or container that holds one.
- **Not yet supported** (each rejected with a message):
  - overrides in a subclass that repeats or adds type arguments its
    parent (or an interface) leaves open, or fixes them to types that
    mention type parameters; a variable of a class type at type arguments
    that every concrete class below it fixes otherwise (`cell(t)` in
    generic code, when `cell` is abstract and its only class below is
    `intcell := class(cell(int))` with an override): it would have no
    initial value; a class that gives two
    interfaces different type arguments, an interface that gives a parent
    interface other than its own type parameters, and a parametric class
    below a non-parametric interface (or one that adds type parameters
    below a parametric interface's implementation).

## Mutation, macros, tooling

- **`set X? = v`** sets the value inside an option
  variable, and fails when the option is empty. It also works as a step of a
  path, as in `set S.Best? *= 7` and `set M[k]? = v`.
- **`let(defs){body}`** makes `defs` visible in `body`
  only. Its value is the body's.
- **Clause macros** (`if{…}`, `for{…}`, `first{…}`, `first(…){…}` and
  `assert{…}`). Each takes clauses in braces, separated by
  `;`, `,` or new lines, run in a failure context; their value is the last
  clause's: a binding's name, or the expression's value.
  - `if{c}` runs `c` and has no value; `if{c} else e` (also `else if{…}`) is
    the value of `c` when it succeeds, else `e`'s.
  - `for{c}` is the array of `c`'s values, for each way its generators,
    filters and bindings succeed: `for{X := 1..4; X * X}`.
  - `first{c}` fails when `c` does, else it is `c`'s value; `first(c){b}`
    runs `b`, which sees `c`'s names, once `c` succeeds, and fails when `c`
    does. Without a body after it, `first(…)` is a call.
  - `assert{c}` is a runtime error (as `Err()`, with no message) unless
    `c` succeeds.
  With no generators (`choice` is not supported), `first` is the first and
  only success, and `first{c}` can only fail when `c` can. These macros
  take no body (`for{c} {b}` is refused), and `first` and `assert` before
  `{` are the macros, not a struct of that name. A void branch makes an
  `if` void (void accepts any value), so `if{X := e} else {Print("none")}`
  is a statement.
- **The command line**:
  - `openverse run FILE [ARG…] [do EXPR]`, and likewise `emit`. The
    arguments are the program's `Args:[]string`, unless it defines `Args`
    itself.
  - With `do EXPR`, `EXPR` runs instead of `Main`, in the context of the
    file's definitions, and its value is printed when it is an `int`, `char`
    or `string`. The expression may fail, which gives exit code 1.
  - A `#!` first line is a `#` comment.

## any

`any` is the top type (Book of Verse ch. 11, #138): every value is an
`any`, and `any(X)` makes one explicitly. Where no type is expected, two
types with nothing in common join at `any`: `if (C?) then 42 else "text"`,
`array{15.61, "Message", 3}` (a `[]any`). Classes with two common
supertypes are still an ambiguity, and an expected type still decides
(`X:int = if (C?) then 1 else "a"` is refused).

Nothing can be done with an `any`: it has no equality (so it is no map
key), no `ToString`, and no cast back. So in Verse Core it is `void`: a
value becomes an `any` by being evaluated.

## Refinement types

A refinement type is an int or a float that meets conditions (Book of Verse
ch. 11, #136):

```verse
age := type{_X:int where 0 <= _X, _X <= 120}
finite := type{_X:float where -Inf < _X, _X < Inf}

Main():void =
    A:age = 25                       # a literal: checked when compiled
    if (B := age[A + 1]) then Print("{B}")   # a cast: fails if not an age
    if (not age[150]) then Print("150 is not an age")
```

- The base is `int` or `float`. Each condition compares the variable with a
  literal number by `<`, `<=`, `>` or `>=` (a float bound has a point;
  `Inf` and `-Inf` may bound a float, NaN may not).
- A literal of the base type is a refined value if it meets the conditions,
  checked when the program is compiled (`A:age = 150` is refused). Any other
  value becomes one by the cast `age[X]`, which fails when `X` is not one.
- A refined value is a value of its base: arithmetic, comparisons, `case`,
  `ToString` and the built-ins see the base, and their results are of the
  base type. `set X op= …` of a refined variable needs a cast.
- A refinement whose interval lies within another's is one of it (#143):
  a `percent` in [0, 1] is a `finite`. An int's strict bound counts as the
  next one (`_X < 10` is `_X <= 9`). The negation of a refined value is of
  an expected refinement whose interval holds the flipped one
  (`NegValue:negative_percent = -MakePercent()`).
- Not supported: overloads on disjoint refinements (refinements of one base
  overlap).

## float

A `float` is an IEEE 64-bit float (Book of Verse ch. 2, #127), except that
it has one NaN, which equals itself, and no negative zero:

```verse
Area(R:float):float = 3.14159 * R * R

Main():void =
    Count:int = 5
    Print("{Area(2.0)} {Count * 1.5} {0.1 + 0.2}")   # 12.56636 7.5 0.30000000000000004
    if (N := Round[2.5], M := Int[-1.7]) then Print("{N} {M}")   # 2 -1
    Print("{1.0 / 0.0} {0.0 / 0.0}")                 # Inf NaN
```

- `+ - * /`, unary `-`, and `set +=, -=, *=, /=`. Dividing by zero gives
  `Inf`, `-Inf` or `NaN`; it does not fail.
- No int converts to a float implicitly. The one mix is `*`: `Count * 1.5`.
- `=`, `<>`, `<`, `<=`, `>`, `>=`. NaN equals NaN, and so `NaN <= NaN` and
  `NaN >= NaN` succeed (the API's reading, #132); otherwise NaN orders with
  nothing: `NaN < NaN` and `NaN <= 1.0` fail.
- `Floor[F]`, `Ceil[F]`, `Round[F]` (ties to even) and `Int[F]` (towards
  zero) give an int. They fail on NaN or an infinity; a result out of the
  int range is the overflow error (the API's integer-bounds error). `Abs`, `Min` and `Max` take floats too; `Min` and `Max` give NaN
  when either is NaN.
- `Sqrt`, `Exp`, `Ln`, `Log(Base, X)` (`Ln(X) / Ln(Base)`), `Pow(Base, E)`,
  `Sin`, `Cos`, `Tan`, `ArcSin`, `ArcCos`, `ArcTan` and `ArcTan(Y, X)` never
  fail; their special values are C's (`Sqrt(-1.0)` and `Ln(-1.0)` are NaN,
  `Ln(0.0)` is `-Inf`, `Pow(0.0, 0.0)` is `1.0`, `Sin(Inf)` is NaN).
  `ArcSin` and `ArcCos` clamp their argument to [-1, 1] (the Book leaves
  that case to the engine). `IsFinite[F]` fails on `Inf`, `-Inf` and NaN,
  and is `F` otherwise. `PiFloat`, `Inf` and `NaN` are constants (#132).
  `Log` divides `Ln`s, so `Log(10.0, 1000.0)` is `2.9999999999999996`.
- A program may define functions named `Round`, `Int` or any of these
  (and constants named `PiFloat`, `Inf`, `NaN`): its definition then
  replaces the built-in for every call, whatever the argument types. A local
  or a method may not take those names; a field may, and in its class's
  methods the name still means the built-in.
- `ToString` gives the shortest decimal that reads back as the float, laid
  out as Python's `repr` (`98.5`, `1.0`, `1e+16`, `1.5e-07`), and `Inf`,
  `-Inf`, `NaN`.

## rational

`X / Y` on ints is a `rational`, and fails when `Y = 0` (Book of Verse
ch. 2, #116):

```verse
Half(X:int)<decides>:rational = X / 2

Main():void =
    if (R := 7 / 2, R = 14 / 4, 3 < R, R < 4) then
        Print("{Floor(R)} {Ceil(R)}")    # 3 4
```

- `int` is a subtype of `rational`: an int passes as one, and an int joins
  a rational to a rational. The reverse needs `Floor` or `Ceil`, which never
  fail on a rational.
- `=` and `<>` compare rationals in lowest terms (`6 / 4 = 3 / 2`). The
  orderings `<`, `<=`, `>` and `>=` compare them exactly; an operand may be
  an int.
- `rational` is a type of variables, parameters, results, fields and
  containers. It is comparable, so it can be a map key.
- There are no rational literals, no arithmetic on rationals (`R + 1`,
  `R / 2`), and no `ToString` of one.

In Verse Core a rational is the tuple of its numerator and denominator, in
lowest terms with a positive denominator. Its parts are 64-bit ints, so
`X / Y` raises the overflow error when the result's numerator or
denominator is out of range, as in `(-2^63) / -3` or `1 / (-2^63)`.

## char32

A `char32` is a Unicode scalar value (`0u…` literals). It is an `int` in Verse Core, so it needs no new value, and the
proofs and the C runtime are unchanged. `=`, `<>`, `<`, `<=`, `>`, `>=` and
`case` work on it, and it has no arithmetic. `ToString` and string
interpolation encode it as UTF-8, its one to four bytes, by code that the
elaborator generates (Core has no conversion from int to char). `=` and `<>`
between values of different types that are the same in Core are an error
(a `char32` or an enum and an `int`, two structs with the same fields, or
containers of such), since they would compare equal there; so are those
between two type parameters, or between one and a type with an `int` or a
tuple, which an instance could make the same. A
non-ASCII character in quotes is refused, with the `0u` literal to write
instead: a `'c'` literal is ASCII.

## Modules

A module groups definitions under a name (#112):

```verse
spell := module:
    Bonus<public>:int = 3
    Base:int = 10                         # internal: only spell sees it
    Inner<public> := module:
        Factor<public>:int = 7
        Scale<public>(X:int):int = X * Factor
    wand<public> := class:
        Power:int
        Cast<public>():int = Power * Inner.Factor + Base

using{spell}

Main():void =
    Print("{spell.Bonus} {spell.Inner.Scale(2)} {Inner.Scale(3)}")
    W:spell.wand = spell.wand{Power := 2}
    Print("{W.Cast()}")
```

- A module is `name := module:` with its definitions indented, or
  `name := module{…}`. It holds functions, constants, structs, enums,
  classes, interfaces and other modules. A constant in a module states its
  type (`X:int = 1`, not `X := 1`). A module is not a value.
- A name is looked up from its definition's module outward, one scope at a
  time, up to the top level. At each scope, the scope's own definitions
  come first, then the members of the modules it opens with `using{M}`.
  If two modules opened at the same scope give the name, it is ambiguous
  and an error. The first definition or module found is the one meant.
- `(M:)F` and `(A.B:)F` are `M.F` and `A.B.F` (#145): values, functions,
  the type `(M:)c` and the construction `(M:)c{…}` (#147).
- `M.F`, `A.B.F`, the type `M.c`, the value `M.c{…}`, a delegation
  `M.D<constructor>(…)` and a qualifier `X.(M.i:)F()` name a member. `M`
  is looked up like any name; if a value is found instead, `.F` is its
  field. Each level used from outside it must be `<public>`, including
  each module of a `using{A.B}`. Members are `<internal>` by default:
  visible in their module and its submodules. A name's overloads are all
  `<public>` or all internal.
- Verse does not allow shadowing. A local, parameter or class member
  (inherited ones included) named like a visible module or module member
  (its own module's, or an open module's) is an error.

Modules exist only in the front end. Each member becomes a definition of
its qualified name before elaboration, and messages show it as `M.F`.

## Programs of several files

`using{"relative_path"}` (or `import{"relative_path"}`) imports a file or a
directory, relative to the importing file (#27). `openverse run|emit|check PATH` takes a file or a directory. A
directory is assembled from its entries in sorted order:

- names starting with `.`, names containing `.ignore`, and files with no `.`
  are skipped;
- `Self.verse` and every other `.verse` file contribute their definitions;
- `Name.txt` gives `Name:string`, `Name.value` gives `Name := (contents)`,
  and `Name.bin` gives `Name:[]int` of its bytes.

A file or directory is not a module (write `name := module:` for one), so
the readings are flat:

- all the definitions join one top level, so a name defined in two files is
  an error;
- a file's `using{M}` opens `M` at the top level, for the whole program, not
  just that file;
- each file is loaded once, so import cycles are harmless;
- subdirectories are flattened;
- other extensions, and `.zip`, are ignored;
- errors in an imported file show its path.

## Concurrency

A function marked `<suspends>` can wait (Book of Verse ch. 14, #156).
openverse supports such functions, `Sleep`, calls between them, `sync`,
`race`, `rush`, `branch`, `spawn`, `task` and `event`.

```verse
Countdown(N:int)<suspends>:int =
    var I:int = N
    loop:
        if (I <= 0) then break
        Print("{I}")
        Sleep(1.0)
        set I -= 1
    N

Main()<suspends>:void =
    Total := Countdown(3)   # prints 3 2 1, one second apart
    Print("done after {Total} seconds")
```

- **`sync`.** Each statement of a `sync:` block is an arm. The arms start in
  source order, each running until it waits or ends before the next starts,
  and the `sync` ends when all have, with the tuple of their values. At
  least two arms must be able to wait.
- **`race`.** The arms start in source order; the first to end wins, and its
  value is the `race`'s (of the arms' common type). An arm that ends without
  waiting wins at once, and the arms after it never start. The losers that
  started are cancelled at once, last started first: each unwinds from where
  it waits, running the `defer:` blocks active there, those of the functions
  it called first.

  ```verse
  Fetch()<suspends>:string =
      defer:
          Print("fetch cancelled or done")
      Sleep(5.0)
      "data"

  Main()<suspends>:void =
      Result := race:
          Fetch()
          block:
              Sleep(1.0)
              "timeout"
      Print(Result)    # fetch cancelled or done, then timeout
  ```
- **`rush`.** As `race`, but the arms that started and have not ended when
  the first ends go on, as tasks of their own, until they end or the
  function that contains the `rush` exits (which cancels them, running
  their defers). A `rush` cannot be in a `loop` or `for` body (the Book's
  rule).
- **`branch`.** The body of a `branch:` runs as a task of its own, at once
  up to its first wait, while the code after it goes on. It shares the
  enclosing function's variables, and it is cancelled (running its active
  `defer:` blocks) when that function exits, by returning, ending or being
  cancelled: after the function's own `defer:` blocks, the last started
  branch first. A `branch` cannot be in a `loop` or `for` body (the Book's
  rule), even through an arm.
- **`spawn`.** `spawn{F(…)}` starts a task running the call, which must be
  of a suspends function or method (`spawn{Agent.Run()}`, also when
  subclasses override `Run`). Its arguments are evaluated at once, and the
  task runs at once up to its first wait. The value is a `task(t)`, where
  `t` is `F`'s result type, and `T.Await()` waits for the task to end and
  gives its result (at once if it has ended). A task is not tied to the
  code that spawned it: it runs until it ends or the program does. `spawn`
  is allowed in any function, immediate ones too, and in a field's default
  (a task per construction that omits the field);
  without a suspends `Main`, a task runs only up to its first wait.
  `T.Cancel()` (in a suspends function) cancels a task that has not ended:
  it unwinds at once, running its `defer:` blocks, or, when a task cancels
  itself, at its next wait. Awaiting a cancelled task cancels the task that
  awaits (and a `Main` that awaits one is cancelled, which ends the
  program); cancelling a task that has ended changes nothing.

  ```verse
  Fetch(Name:string, D:float)<suspends>:string =
      Sleep(D)
      "{Name} data"

  Main()<suspends>:void =
      A := spawn{Fetch("a", 2.0)}
      B := spawn{Fetch("b", 1.0)}
      Print(B.Await())    # after 1 second: b data
      Print(A.Await())    # after 2 seconds: a data
  ```
- **`event`.** An `event(t){}` has `E.Await()`, which waits for the next
  `E.Signal(X)` and gives `X`, and `E.Signal(X)`, which wakes every task
  waiting at that moment, each with `X` (the API's reading; the Book's text
  says both "each awaiter" and "exactly one"). The woken tasks go on in the
  scheduler's order (`Main`, then tasks in the order they were started,
  arms in source order), not in the order they began waiting. A `Signal` with no one waiting is lost, and `Signal`
  itself never waits. `event()` is an event without a value (`event(void)`),
  with `E.Signal()` and `E.Await()`. A `sticky_event(t)` (or
  `sticky_event()`) is an event that keeps its last signal: an `Await`
  after a `Signal` gives that value at once. `subscribable_event` is not
  supported (openverse has no function values).
- **Arms.** Arms share the enclosing function's variables. An arm is a
  scope of its own, which `break` cannot leave. A `return` in an arm
  returns from the enclosing function: the arm's defers run, then the other
  arms that started are cancelled (last started first), then the defers of
  the scopes around the `sync`, `race` or `rush`. A `return` in a `branch`
  is an error, as in a `defer`.
- **Effects.** `<suspends>` and `<decides>` exclude each other. A suspends
  function, `Sleep`, `sync` and `race` can be used only in a suspends
  function, and not in a failure context (an `if` condition, a `for`
  filter, a `case` pattern, a `<decides>` call's arguments) nor in a
  `defer`. A method may be `<suspends>` (an override must be too, and
  only when what it overrides is). Code generic over a class can call one
  that a subclass fixing its type arguments overrides (`int_box :=
  class(box(int))`), under the refinement that gives (#142, #171); not
  yet when the override has type parameters (its class's or its own). A
  `<suspends>` constructor is not supported. `<suspends>` combines with the heap effects
  (`<computes>`, `<reads>`, …): waiting has none.
- **Time.** The schedule is deterministic: a virtual clock counts ticks, 30
  per second, and ticks in which nothing can run are skipped. In each tick,
  `Main` goes on first, then each task in the order they were spawned, then
  again while a task ended (so that those waiting for it go on in the same
  tick). Arms that can go on in the same tick do so in source order. `Sleep(S)`
  resumes after `Round(30·S)` ticks, at least one, so it always yields;
  `Sleep(Inf)` never resumes; a negative or NaN `S` returns at once.
- **The program.** A suspends `Main` runs under the scheduler. The program
  ends when `Main` does, even if tasks are still running. If `Main` waits
  and no task can run again (for example after `Sleep(Inf)`, or awaiting a
  task that never ends), it ends as `Err()` does: exit 2.
- **Lowering.** The front end compiles each suspends function into Verse Core:
  a frame object holds its variables, and a resume function runs it from
  one suspension point to the next (see DESIGN.md). Nothing changes in
  Verse Core, the proofs or the C runtime. A call site keeps its callee's
  frame, so a loop of calls allocates once.
- **Generic functions.** A generic function with a `branch`, a `rush`, or a
  `spawn` whose call's arguments or result have types that mention its
  type parameters, and a generic immediate function with any `spawn`, is
  compiled once for each type it is used at (#174), as the scheduler's
  tasks have no type arguments; so is a generic function that uses such a
  function at its own type parameters. Such a function calling itself at
  ever bigger types (`F(X:t)` calling `F(array{X})`) would need endlessly
  many copies and is refused: a program may need at most 500 copies, at
  types of at most 2000 parts.

## Readings openverse takes

| Question | Book | openverse |
|---|---|---|
| `int` range | arbitrary precision on VerseVM; 64-bit with a runtime error on BPVM (§4.1) | **BPVM**: 64-bit, overflow is a runtime error (not a failure), never wrap-around |
| `X = Y` result | the operators page says `logic`; elsewhere the left operand (§5.4) | the left operand |
| Associativity of comparisons | table: right; text: left; chains are special (§5.1) | chains: every adjacent pair checked, each operand evaluated once, result is the leftmost |
| Value of a successful `not e` | unspecified | `void` |
| Type of `if` without `else` | unspecified | `void` |
| A failing `for` body | unspecified (VC: the `for` fails) | the `for` fails (as in VC) |
| A failing `for` source | "the iteration is skipped" | zero iterations |
| `?` on other values | conflict (§6.1) | only `logic` and `?t` (the API's typed reading) |
| Output inside a failed failure context | unspecified | rolled back with the writes (transactional `Print`) |
| `Main` failing | (no entry point in the book) | exit code 1; output already printed stays |
| `return` inside a failure context | unspecified | leaves the function; no rollback of what the condition did |
| Scope of the operands of `A and B` | "Variable bindings do not escape from logical operations" (§3.4) | each operand is its own scope: names defined in `A` are not visible in `B`, and names from neither side escape the `and` |
| Comparability | `comparable` covers the primitive types, enums, structs and containers of comparable types (§4.9) | so is every openverse type, except a type parameter not declared `subtype(comparable)` and the containers of one |
| Inferring type arguments | not described | first-order matching against the expected result type, then the arguments; no subtyping other than `false` (matches anything) and `void` (accepts anything) |
| Access specifiers other than `<public>` | `<internal>` (the default), `<private>`, `<protected>`, … (ch. 16) | a module member is `<public>` or internal (visible in its module and its submodules); other specifiers, and a struct field's, are accepted and not enforced |
| `ToString` of a float | "the shortest" (an example: `98.5`) | the shortest decimal that reads back as the float, the closest of the shortest, in Python's `repr` layout (exponent at `≥ 1e16` and `< 1e-4`); `Inf`, `-Inf`, `NaN` |
| `NaN < X` | not stated | fails (IEEE: NaN orders with nothing); `NaN = NaN` succeeds (the Book) |
| `=` between different types | not stated | refused when two scalar types (int, float, char, …) meet at the same place, also inside containers (`array{1} = array{1.0}`), as Verse Core holds them differently |
| Ordering of rationals | not stated (§2 lists `<` … for `int` and `float`) | exact (by continued fractions, so it cannot overflow), and an int compares with a rational |
| `Sleep(0.0)` | "may resume in the same tick" (ch. 14); the API reference: it always yields | always yields: resumes in the next tick (#156) |
| `Sleep(S)` rounding | rounded up to whole ticks (ch. 14) | `Round(30·S)` ticks, at least one: rounding to the nearest keeps `Sleep(0.1)` at 3 ticks despite binary floats (#156) |
| End of a program with tasks | not stated | the program ends when `Main` does; a `Main` that waits with no task able to run is an error (exit 2) (#156) |
| Extent of a `<#>` comment | "everything indented by four spaces on subsequent lines" (§1.1) | the rest of the `<#>` line and every following line indented more than that line, whatever the amount (blank lines included); `<#>` may also follow code on a line |

## Not supported in v1

arithmetic on rationals (see [rational](#rational)), float functions beyond those of [float](#float),
the class features listed under [Classes](#classes), struct methods (Verse structs have none; classes do),
`weak_map`, module paths `using{/Verse.org/…}` (accepted and ignored), overloading beyond [Overloading](#overloading), nested
functions, concurrency beyond [Concurrency](#concurrency) (`subscribable_event`; #156), and effect checking
other than `<decides>` and the heap effects (`<converges>` is accepted and
ignored).
