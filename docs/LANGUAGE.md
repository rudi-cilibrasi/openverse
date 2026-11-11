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

- The language: [Supported](#supported) · [Source text](#source-text) · [Parametric functions](#parametric-functions) · [Function values](#function-values) · [defer](#defer) · [Overloading](#overloading) · [Parametric structs](#parametric-structs) · [Classes](#classes) · [Mutation, macros, tooling](#mutation-macros-tooling) · [Choice](#choice)
- More types: [any](#any) · [Refinement types](#refinement-types) · [float](#float) · [rational](#rational) · [char32](#char32)
- Programs: [Modules](#modules) · [Programs of several files](#programs-of-several-files) · [Concurrency](#concurrency)
- [Readings openverse takes](#readings-openverse-takes) · [Not supported in v1](#not-supported-in-v1)

## Supported

| Area | Supported | Book |
|---|---|---|
| Comments | `#` to the end of the line, nested `<# … #>`, `<#>` indented comments (the rest of the line and every following line indented more than it; see [Source text](#source-text)) | ch. 0 |
| Literals | `int` (decimal, `0x` hex; must fit in 64 bits), `'c'` `char` (`c` printable ASCII U+0020–U+007E, or an escape), `0oHH` `char` code unit (one or two hex digits, not octal: `0o41` is `'A'`, `0o9` is a tab), strings with escapes and `{expr}` interpolation, `true`, `false`, `0uHHHHHH` `char32` (a Unicode scalar value, up to `0u10FFFF`, no surrogates), `float` `1.5`, `2.0e-7`, `1e3` (digits, then a point and digits or an exponent or both; the nearest double) | §1.3–1.7 |
| Types | `int`, `logic`, `char`, `char32`, `any` (see [any](#any)), `rational` (see [rational](#rational)), `float` (see [float](#float)), refinement types `type{_X:int where 0 <= _X, _X <= 120}` (see [Refinement types](#refinement-types)), `string` (= `[]char`), `[]t`, `?t`, `tuple(…)`, `void`, function types `type{_(:int)<decides>:int}` and `int->int` (see [Function values](#function-values)); a tuple converts to an array of its elements where an array is expected, and compares with an array as one (`array{1,2} = (1,2)`) | ch. 2–3 |
| Definitions | top-level functions `F(X:t, …)<effects>:t = body`, top-level constants `C:t = e` / `C := e`; locals `X := e`, `X:t = e`, `var X:t = e`; no shadowing | §3.1–3.4 |
| Mutation | `set X = e`, `set X += e` (`-=`, `*=`), `set A[i] = e` (fails out of range; returns `e`), and paths `set S.F.G = e`, `set A[i][j] op= e`, `set M[k].F = e`: indices and keys evaluated once, left to right, then the new value (for `op=`, after the old one is read: `set X += e` is `set X = X + e`), then the variable rebuilt; an index out of range or a missing intermediate key fails, while the last key of a path inserts | §3.3, §3.5, §9.3 |
| Blocks | indented (`:`), braced (`{ }`), inline (`then`/`do`), `block:`, `( a; b )` sequences | §2.2–2.4 |
| Operators | `* + -`, unary `-`, comparisons `= <> < <= > >=` (failable, return the left operand, chains check every pair), `and`, `or`, `not` (below the comparisons, above `and`: `not X = Y` is `not (X = Y)`), `?`, `.Length`, `A[i]`, `T(k)` | ch. 4 |
| Failure | failure contexts (`if` conditions, `for` clauses, `option{}`, `logic{}`, `not`, left of `or`, `<decides>` bodies) with rollback of `var` writes **and output** | ch. 8 |
| Control | `if`/`else if`/`else` (all styles, `if:`…`then:`), `for` with `X : array`, `I -> X : array`, `X := a..b`, filters, bindings, several generators (cartesian product), `loop`/`break`, `return`, `case` with literal patterns and `_` | ch. 7 |
| Choice | `a \| b \| …` with several values in spatial order, in a clause of an `if` condition, `first{…}`, `option{…}`, `logic{…}`, `not` or `or` (the first success) or of a `for` (all of them), also inside expressions (`(1 \| 2) + (10 \| 20)`, `X = 1 \| 2`); see [Choice](#choice) (#208) | (the Verse Calculus) |
| Functions | a tuple argument expands into several parameters (`Describe(MyTuple)`), several arguments make a single array parameter (`Sum(1, 2, 3)`) (#134, #140; the array form for a plain call only, and a method's, an overloaded or a generic function's tuple is typed without the parameters' types); recursion, mutual recursion, `<decides>` (called with `F[…]`; other functions with `F(…)`), named parameters `?P:t = default` passed as `?P := e` (positional, then named as written, then defaults; a default may use the parameters before it, and a method's default the method's fields; a call dispatched to an override evaluates that override's own default for an omitted argument; a default is evaluated at the call, its effects counting as the caller's, and cannot return, break or use itself), the heap effects `<computes>`, `<reads>`, `<writes>`, `<allocates>`, `<transacts>` (checked, see [Classes](#classes)), other effect specifiers accepted and ignored | ch. 6, 13 |
| Parametric functions | `F(X:t, … where t:type, u:subtype(comparable))`: type parameters in parameter types, the result type and local declarations; type arguments inferred at each call (see [Parametric functions](#parametric-functions)) | Types: where clauses |
| Structs | `name := struct:` with typed fields and defaults, `name{F := e, …}` (each field given at most once, evaluated in declaration order), `S.F`, `set S.F = e` / `op=`, structural equality (a struct is the tuple of its fields in Verse Core) | ch. 9 |
| Parametric structs | `pair(t:type, u:type) := struct:`, the type `pair(int, string)`, values `pair(int, string){First := 1, Second := "a"}` (or `pair{…}` where the expected type gives the type arguments); see [Parametric structs](#parametric-structs) | ch. 9 |
| Classes | `name := class:` and `name(t:type) := class:` with fields and methods; `class(parent, interface, …)`, `interface`, `<abstract>`, `<override>`, `<final>`, `(super:)`, virtual dispatch, casts `T[X]` and `T(X)`; no `var` fields; see [Classes](#classes) | ch. 10 |
| Enums | `name := enum:` / `enum{A, B}`, `name.A`, equality, `case` that needs no `_` when every value is named (an enumerator is its index in Verse Core); `enum<open>` may gain values, so a `case` on one needs `_` or a failure context (`<closed>` is the default) | ch. 9 |
| Maps | `[k]v`, `map{k => v, …}` (a key given twice keeps its last value, at its last position), `M[k]` (fails on a missing key), `set M[k] = v` (insert or update, never fails), `set M[k] op= v` (fails on a missing key), `.Length`, `for (V : M)`, `for (K -> V : M)` in insertion order, `ConcatenateMaps(M1, M2, …)` (a later map's value wins for a key, which keeps its first position), order-sensitive equality (a map is the array of its pairs in Verse Core) | §3, §9.3 |
| Array methods | `A.Slice[i, j]`, `A.Slice[i]`, `A.Find[x]`, `A.RemoveElement[i]`, `A.RemoveFirstElement[x]`, `A.Remove[i, j]` (half-open), `A.ReplaceElement[i, x]`, `A.ReplaceFirstElement[x, y]`, `A.Insert[i, B]`, `A.Last[]`, `A.Last[n]` (the element n before the last) (all failable); `A.RemoveAllElements(x)`, `A.ReplaceAllElements(x, y)`, `A.ReplaceAll(Pattern, Replacement)` (contiguous subarrays, left to right, not overlapping; an empty pattern changes nothing), `Concatenate(A, B, …)` or `Concatenate(Arrays)` (#150) (never failing) | §9.1 |
| Built-ins | `Print(s)`, `ToString(x)` (int, float, char, string), `Floor[F]`, `Ceil[F]`, `Round[F]`, `Int[F]` (of a float, failable), `Floor(R)`, `Ceil(R)` (of a rational or an int, never failing; `Floor(X / Y)` fails when `Y = 0`, as `X / Y` does), `Quotient[X, Y]`, `Mod[X, Y]` (Euclidean), `Abs`, `Min`, `Max`, `Err()` | API reference |
| Modules | `name := module:` (nested), `M.F`, `A.B.F`, the types `M.c` and values `M.c{…}`, `(M:)F`, `using{M}` at file or module scope, `<public>` members (`<internal>` is the default); see [Modules](#modules) | ch. 16 |
| Concurrency | `<suspends>` functions and methods, `Sleep`, `sync`, `race`, `rush`, `branch`, `spawn` with `task(t)` and `Await`, `event(t)` with `Signal` and `Await`, `subscribable_event(t)` (or `subscribable_event()`) with `Subscribe` and `Cancel` (see [Function values](#function-values)), cancellation with `defer:`, under a deterministic scheduler; see [Concurrency](#concurrency) | ch. 14 |
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

## Function values

A function type is written `type{_(:t₁, :t₂)<effects>:r}` or `t₁->r` (Book
of Verse ch. 6); `tuple(t₁, t₂)->r` takes two parameters, as a tuple
flattens into parameters, and `->` binds loosest (`[]int->int` takes an
array). A top-level function, or a method of an object, named without a call is
a value of its function type (#210):

```verse
Twice(F:int->int, X:int):int = F(F(X))
Map(Xs:[]t, F:type{_(:t):u} where t:type, u:type):[]u = for (X : Xs) { F(X) }
Double(X:int):int = 2 * X
Main():void =
    Print("{Twice(Double, 3)}")      # 12
    Fs:[]int->int = array{Double}    # arrays, options, fields, var…
```

- A value is called like a function: `F(X)`, or `F[X]` when its type is
  `<decides>`. A `<suspends>` type's values are called in suspends code.
- A function fits a function type with at least its effects: a function
  without `<decides>` is also a `type{_(:int)<decides>:int}` (fewer
  effects make a subtype). Its parameter and result types must match,
  except that a function named where a closed function type is expected
  is a value of it if it fits it by variance (#214): its parameters may be
  above the type's (`Describe(A:animal)` is a `type{_(:dog):string}`) and
  its result below (`Count():int` is a `type{_():rational}`), with `int`
  below `rational` and a class below the classes above it. A method does
  too (#231) when the class that gives the receiver's value of it (the
  nearest that declares or overrides it) has no type parameters:
  `Obj.Describe` is a `type{_(:dog):string}`, holding `Obj`, evaluated when
  the value is made. (A subclass `gsub(t) := class(base)` may have them;
  `abox := class(box(animal))` using `box(t)`'s method may not.) And a
  tuple flattens and unflattens between parameters there (#231):
  - a function with one `tuple(int, string)` parameter is a
    `type{_(:int, :string):int}` (the call makes the tuple);
  - a function of two parameters is a `type{_(:tuple(int, int)):int}`
    (the call takes it apart);
  - a generic one at an instance, its single parameter standing for the
    whole tuple: `Id(X:t):t` is a `type{_(:int, :string):tuple(int, string)}`. A
  value of one function type does not convert to another by variance.
- Function values are not comparable and have no `ToString`.
- A method as a value, `C.Add` (or `Add` in a method of the class), holds
  its receiver: calling it calls `C.Add`, the receiver's class's
  implementation, and sees and changes `C`'s fields. Its type is the
  method's in `C`'s static class, so an override's narrower result type
  is the value's (#219), or, where a function type is expected, that of
  the class above that declares or overrides it with that type.
- A generic function is a value where a closed function type that is an
  instance of its type is expected (`F:int->int = Identity`, or an
  `int->int` parameter); a `subtype(comparable)` type parameter only at a
  type built from the primitive comparable types. Not where the type
  mentions type parameters (`Map(Xs, Identity)` with `Map` over
  `type{_(:t):u}`).
- Generic methods, overloaded functions and methods and ones with named
  parameters cannot be used as values, nor can a method whose type repeats,
  nests or leaves out one of its class's type parameters (`box(t)`'s
  `Same(X:t):t` is not done yet, #209; its `Size():int` leaves `t` out). Lambdas and
  nested functions are not released in Verse, so there are none.

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
    fine (they are only reached by code that never runs), except in code
    generic over it at type arguments that every class below it fixes
    otherwise (see *Not yet supported* below).
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
  it has as many Verse Core type arguments as the class that declares it
  (its parent's, then its own type parameters that are not one of them:
  `dup(t)` has `pair`'s two, `t` and `t`). It may fix
  some of them to closed types (#142): `int_box := class(box(int))`
  overrides `box(t)`'s `Get():t` with `Get():int`, and code generic over
  `box(t)` (or over an interface `box` implements) runs it, typed under
  `t = int`. It may also repeat them or fix them to types over its others
  (#209): `dup(t) := class(pair(t, t))` overrides `pair(t, u)`'s
  `Get():t` with one that returns its `u` field, run under `u = t`, and
  `optpair(t) := class(pair(?t, t))` overrides it with `Get():?t`. The
  refinement is the most general one that makes the receiver's type
  arguments fit the class (so a type-equality witness `refl(t) :=
  class(eqw(t, t))` casts an `a` to a `b` through any `eqw(a, b)`), and
  the dispatch skips the classes that no instance of the receiver's type
  fits. A class can also have type parameters of its own that the type
  arguments it gives its parent do not give as a whole, existentially
  quantified as in a GADT (#209): `pairE(a, b) := class(expr(tuple(a,
  b)))`, whose `a` and `b` occur only inside `expr`'s argument, and
  `fstE(a, b) := class(expr(a))`, whose `b` does not occur at all. Code
  generic over `expr(t)` dispatches to their overrides of `Eval():t`: the
  dispatch opens `a` and `b` as types it has no names for, refines `t` to
  `tuple(a, b)` for a `pairE`, and runs `pairE`'s `Eval` at them. Such
  an object carries a value of each of those types, hidden, which its
  overrides start their variables of those types with. Its overrides may
  be `<suspends>` (#251): `pairE`'s `Eval()<suspends>:tuple(a, b)` can
  wait, and its caller gets the result at its own `t`. A class below
  such a class can fix or repeat those type arguments (`leaf :=
  class(mid(int, string))` below `mid(a, b) := class(expr(tuple(a, b)))`)
  and override too. A cast in generic code that holds only under such a
  refinement is pattern matching on the class, as in a GADT (#243): as a
  clause of an `if`'s condition, `D := T[X]` types the branch it guards,
  and the clauses after it, under the refinement, where the code's type parameters are unified as `T`'s
  type arguments say (written types in the branch included):

  ```verse
  Eval(E:expr(t) where t:type):t =
      if (L := lit[E]) then L.V                         # t = int here
      else if (A := add[E]) then Eval(A.L) + Eval(A.R)  # t = int here
      else Err()
  ```

  A later clause may be such a cast too (#243), when the clauses before it
  print nothing, change no object and call nothing, so that its failure
  has nothing of theirs to undo: `if (N := Ns[0], N > 0, D := dup[P])` is
  `if (N := Ns[0], N > 0) then (if (D := dup[P]) …)`, the `else` the same
  in both.

  A cast can also open type arguments the object's type has no names for
  (#250): `if (P := pairE[E]) then (Eval(P.L), Eval(P.R))`, for
  `E:expr(t)`, types the branch with `t = tuple(a', b')`, where `a'` and
  `b'` are `pairE`'s `a` and `b`, unknown but fixed for the branch; their
  values, which the branch's own generic calls at them need, come from the
  object, which holds them in hidden fields as #209's existential classes'
  objects do. An opened parameter is as comparable as the one it stands
  for, and also when a comparable type parameter's refinement mentions it
  (`t:subtype(comparable)` refined to `tuple(a', b')`), as the object's type
  argument for `t` is then comparable.

  The branch is compiled as a function of its own, generic over the
  enclosing function's type parameters, that takes the object (as `D`) and
  the locals the branch uses, at their refined types; the `if` becomes a
  dispatch to it, which Verse Core types as it types a refined method call
  (`Typed.dispatch`), so nothing is assumed in Verse Core. In a
  `<suspends>` function the branch and the `else` may suspend (#243): the
  branch's function is then `<suspends>`, and the `if` a suspends call of
  it, cancelled as any (its `defer:`s, then the caller's). A `branch` or
  continuing `rush` arm started there belongs to the enclosing source
  function (#419): it can outlive the cast and is stopped when that source
  function exits, after its own defers, in the documented task cleanup
  order. The cast's lexical defers still run when the cast finishes.
  The existing restrictions on task starts in loop/for bodies and refining
  casts in concurrent arms apply through lifted branches too. In a
  `<suspends>` source function, mutable captures share their source storage
  (#419). Writes are visible
  to both the branch and earlier background tasks across waits; cancellation
  also exposes the latest value to enclosing `defer:`s. Ordinary local copies
  and saved return operands keep their captured values. In an immediate
  source function, a `var` from outside the branch that it sets is copied
  in and copied back after the `if` (#243). A
  `return` in the branch, or a `break` that leaves it, makes its function
  return what to do, which the caller then does after the `if` (#243): the
  enclosing function returns, or the loop is left, once the `var`s it set
  have their values. Where the `if`'s value is used, its type must be known
  for that (written, given by where it is, or the `else`'s) unless the
  branch always returns or breaks. In a method, the branch names `Self`'s
  fields and methods as anywhere in the method (its function takes `Self`
  too), and its `(super:)M(…)` calls the implementation the method's class
  inherits, as anywhere in the method (#243; not an overloaded method's,
  for now). Nor can such a cast be in a `defer:`,
  a constructor's items, a class's `block:` clause, a field's or
  parameter's default, or an arm of `sync`, `race`, `rush` or `branch`.
  An interface can be parametric too (#53):
  `container(t) := interface: Get():t`, with `box(t) := class(container(t))`.
  A class gives the interfaces above it its first Verse Core type
  arguments (`box(t)` gives `container` `t`; a class implementing
  `container(t)` and `sink(u)` cannot), so code generic over `container(t)`
  dispatches to `box(t)`'s methods and casts `container(t)` to `box(t)`.
  Its other type parameters are like those a class adds to its parent's
  (#209): `pairbox(t, u) := class(container(t))`, or `box(t) :=
  class(shower)` below an interface without type parameters, holds a
  value of each, hidden, and code generic over the interface dispatches to
  its overrides by opening them (#276). An interface can so be a GADT's
  root: `expr(t) := interface: Eval():t` with `pairE(a, b) :=
  class(expr(tuple(a, b)))`.
  An interface's fields are typed as it gives them. Code generic over the
  interface reads and writes a field that sits at different places in its
  classes also when a class fixes or repeats its type arguments, under
  the refinement that gives (#157, #209). The same goes for a
  field two interfaces both declare, `x(t)`'s `F:t` and `y(t)`'s `F:int`,
  in a class that fixes `t` to `int`: it is read and set through either
  interface, and through a class below `y` whose subclass also
  implements `x` (#205). An interface that extends a parametric interface
  may give it any type arguments, as a class may its parent: a class below
  `c2(t) := interface(container([]t))` is a `container([]t)`, and code
  generic over `container(u)` reaches it with `u` as `[]t` (#53), also
  through a default `c2` gives one of `container`'s methods, which means
  in every class what it means in `c2`: its names, its parameters and
  their defaults, and `(super:)` resolve as in `c2`, whatever members the
  class adds (only a method of `c2` used as a value, `H := F`, is refused
  where the class overloads it); so may
  one without type parameters (`intI := interface(container(int))`). A
  class may give the interfaces it lists any type arguments
  (`both(t, u) := class(container(t), sink(u))`, `c := class(i1(int),
  i2(string))`): a reference to an interface that a class gives type
  arguments other than its own first ones, in order, relates them to each
  class's through the class's view of it (#351), so calls through it
  (`<suspends>` ones and named arguments' defaults too), generic code over
  it, upcasts to the interfaces above it and casts back work as for any
  interface, also for classes below that fix some of those type arguments
  (`ib := class(both(int, string))`) or add their own, and its fields are
  read and set through it too (each class's, at its own place).
  The interfaces a class lists may not reach one interface at two instances
  (`class(pi(int), pi(string))`). Inherited field defaults see their
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
  - a cast from a reference to an interface that a class gives type
    arguments that are not a prefix of its own, or to one above it (see
    above, #351), to a class or
    interface with type arguments, its own or ones it fixes (`c :=
    class(i1(int), i2(string))`), other than as a clause of an `if`'s
    condition (the first, or one after clauses that print, change an
    object and call nothing), whose branch is then a function of its own
    as described above (#243), or to one neither above
    nor below it, and a named argument's default computed by code (not a
    literal) in a call through one, or to a class that fixes type
    arguments from generic code, when it reads the receiver (its field),
    mentions the type arguments the dispatch opens, or uses an argument at
    a type the dispatch refines (#351: others are evaluated in the call, as
    that class's, once); a cast `T[X]` whose type
    arguments agree with `X`'s only under a refinement (`dup[P]` for
    `P:pair(a, b)`) other than as a clause of an `if`'s condition (the
    first, or one after clauses that print nothing, change no object and
    call nothing, #243), whose
    branch has a `return` or a `break` that leaves it where the `if`'s value
    is used at a type not known there, whose branch calls
    `(super:)` of an overloaded method, or in a `defer:`, a constructor's items, a class's `block:` clause, a default
    or a concurrent arm (#243); a variable, in generic code, of a class or
    interface type that requires an instance of itself (`Next:node(t)`)
    at type arguments that every class below it fixes otherwise: its
    hidden placeholder object (#157) would have to hold itself (no program
    can build an object of such a type: each would need another first,
    so use `?node(t)` for a link that may be absent); and, in code generic over an interface's parent, a
    cast to an interface that gives that parent type arguments of its own
    (`c2(t) := interface(container([]t))`) whose type parameters would be
    unknown (#53).

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
  Without a [choice](#choice), `first` is the first and only success, and
  `first{c}` can only fail when `c` can. These macros
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

## Choice

A choice `a | b | …` has several values: `a`'s, then `b`'s, and so on
(the [Verse Calculus](https://doi.org/10.1145/3607845)'s choice; #208).
The failure context it is in takes them:

```verse
Main():void =
    for (X := 1 | 2, Y := 10 | 20):    # a for takes all of them
        Print("{X + Y}")              # 11, 21, 12, 22
    if (X := 1 | 2 | 3, X > 1):       # an if takes the first success
        Print("{X}")                  # 2
    if (F := first{X := 4 | 6 | 9; X > 5; X}) then Print("{F}")   # 6
```

- **Order.** The values come in *spatial* order, which is fixed by where
  each choice is written, not by when it runs. The leftmost choice varies
  slowest, as the generators of a `for` do. A nested choice is spliced in:
  `(1 | 2) | 3` is `1 | 2 | 3`.
- **Who takes them.** A `for`, or `for{…}`, takes every value. An `if`
  condition, `if{…}` and `first{…}` take the first success, and the
  alternatives after it never run: `if (X := 5 | Err())` is not an error.
  An alternative that fails gives no value, and a condition with no
  success fails.
- **Effects.** The code before a choice runs once. Each alternative then
  runs the rest of the clauses.
  - In an `if` condition or `first{…}`, an alternative that leads to no
    success is rolled back, output included, as any failure context is,
    and the next one starts from the state the choice was reached in.
  - In a `for`, a choice is one more generator. An alternative whose own
    clauses (up to the next generator) fail is rolled back. One whose
    clauses succeed keeps their effects, even when the generators after it
    give no value, and each value runs the body, whose effects stay too.
    That is how every generator of a `for` behaves.

  ```verse
  var N:int = 0
  if (X := (set N = 1; 1) | (set N = 2; 2), X > 1) then Print("{X} {N}")   # 2 2
  ```
- **Type.** The written type (`X:int = 1 | 2`), or the type of the
  variable or path that `set` writes, else the join of the alternatives'
  types, as for `if`'s branches.
- **`set L = a | b`** evaluates as `set` does: the indices of `L`'s path
  first, then for `op=` the old value, then the choice, so each alternative
  only runs the assignment.
- **Where.** A choice is taken by an `if` condition, the clauses of a
  `for`, `first{…}`, `first(…){…}`, `if{…}`, `for{…}`, `assert{…}`,
  `option{…}`, `logic{…}`, `not`, and the left of `or`. In their clauses, a choice can
  be a binding's value (`X := a | b`, `X:t = a | b`, `set X = a | b`,
  `var X:t = a | b`), a clause of its own, or inside an expression. It is
  then *lifted* out of its clause, as one more clause before it, with the
  code that runs before it bound to names first, so that it still runs
  first and once:

  ```verse
  for (Y := F() + (1 | 2)) { … }       # as: T := F(), C := 1 | 2, Y := T + C
  if (X = 1 | 2 | 3) then …            # X is 1, 2 or 3
  if (H := Half[3 | 5 | 8]) then …     # the first argument Half succeeds with
  ```

  Lifting goes through arithmetic, comparisons, calls and indexing,
  member access, `?`, tuples, arrays, maps and string interpolation, in the
  order they are evaluated:
  - a call's or an index's head is evaluated before its arguments: a
    variable holding an array, map or function, a field (read whole), a
    method's receiver, or any other expression (`Arr()[0 | 1]` calls `Arr`
    once);
  - in a comparison chain, the pairs before the choice are checked first,
    so the chain stops before it when one fails;
  - a name that is no value (a function, class, module, enumerator, `true`,
    `false`) and a literal, `array{}` or `map{}` stay in place, so they keep
    the type their place expects, and so do arrays, tuples, maps and
    options made of them;
  - every other operand before a choice is bound to a name first, so it is
    read where it is written, even if an alternative changes it (a `set`,
    or a method changing a field);
  - `set L op= R` evaluates `L`'s indices, then for `op=` its old value, then
    `R`'s lifted code, as `set` does. A choice or a call with several values
    in `L`'s indices is lifted there, first (#283): `for (set A[0 | 1] = 5)`
    sets `A[0]`, then `A[1]`, each index a generator. So does such a `set`
    inside `not (…)` or on the left of `or`, which take its first success
    (#283): `(set A[5 | 1] = 8) or …` sets `A[1]`.

  An `if` chain whose branches are choices, plain values,
  expressions with choices or calls of functions with several values in
  them, or blocks with them (whose names are the branch's own, as any
  block's) may stand where a choice may (#235, #283). Its
  conditions run once and pick a branch, whose values are then the
  `if`'s, seeing the names its conditions bind:

  ```verse
  for (Z := if (V := M?) then (V | V * 10) else 0) { … }   # V, V * 10; or 0
  for (Z := if (V := M?) then Two(V) else Down(2)) { … }   # Two's values; or Down's
  ```

  An `if` chain without a final `else` still has type `void`. Each value
  of the selected branch gives one `void` result. If no condition
  succeeds, the implicit branch gives one `void` result.

  The `if` itself adds no choice (#331): only the choices the program
  reaches are generators. In a `for`, when the branch it picks is a plain
  value, a value the filters after it reject undoes what came before it,
  as the same function written with a `return` does (#314). When that
  branch is a choice, the choice is a generator, which keeps it.

  A class cast in the condition can refine its selected branch's type
  arguments (#243), including written types that use that refinement. In a `for`,
  this currently requires a non-suspending consumer whose body has no
  non-local exit or non-rollback operation. A body may fail: this stops
  the whole `for` and retains that iteration's effects, just as in an
  ordinary `for`. An enclosing failure context can still undo them.
  Its suffix must also permit a shared continuation; lazy calls remain
  unsupported. Other contexts remain tracked in #417. Failure of the selected branch's
  alternatives does not select the `else` branch.

  A choice inside a block is lifted with the block's clauses (#283): they
  become the failure context's, in order, so what they do is undone or kept
  as its own clauses' effects are, and the block's last expression is the value. The
  block's names stay its own, and, as for any block, cannot be names
  already in scope:

  ```verse
  for (X := block{ Y := 1 | 2; Y * 10 }) { … }   # 10, 20
  ```

  A block's own `defer:` (or a function's, below) runs as each value
  leaves it (#283), as its lowering places it, after the rest of its scope:
  once the value is computed, before the clauses after it, last registered
  first. A value whose clauses fail runs none, since what they did is
  rolled back with them:

  ```verse
  for (X := block{ defer: Print("d"); Y := 1 | 2; Y * 10 }) { Print(X) }   # d 10 d 20
  ```

  A choice inside a struct or class construction is lifted as one in a
  call's arguments, in the order the construction evaluates its fields: its
  type's declaration order, not as written (`pt{Y := F(), X := 1 | 2}`
  takes X's value first, then calls `F`). A call's named arguments are
  lifted after its positional ones, in the order written, as a call
  evaluates them (the defaults of those omitted come after):
  `F(?C := G(), 1 | 2)` takes the choice, then calls `G`. Nothing is lifted from the body
  of `first{…}`, `spawn`, `branch`, `sync`, `race`, `rush` or `defer:`:
  such a body takes its own choices or runs apart.

  Refused for now: a choice inside a construction where a field it
  does not give, with a default that is more than a literal, comes before
  the choice (the default runs in its place); an
  alternative of a `set`'s choice, either side of `and`, the right of `or`,
  a range, or a block with a range of its own as a branch; and
  a choice anywhere outside these failure contexts. (A field reached
  through a receiver that is not a variable or `Self`, as `F().Items[…]`,
  is read after the choice, since only the receiver's value is bound
  first.) A `break` in the clauses of an `if` or `first{…}` with a choice
  is refused. `first{…}` with a choice can fail, so it must be in a
  failure context.
- **Functions with several values** (#235). A top-level function whose
  body has a choice that nothing in it takes has several values, and a call
  of it is a choice: it goes where a choice can go, and its values come in
  the callee's spatial order, at the call's place.

  ```verse
  Digit():int = 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
  Main():void =
      for (X := Digit(), Y := Digit(), X + Y = 9, X < Y) { Print("{X}{Y}") }   # 09 18 27 36 45
  ```

  A choice's alternatives may have several values themselves, calls of
  such functions or choices inside expressions (`C():int = A() | B()`,
  `X := Upto[1, 3] | 9`): their values come in order, alternative by
  alternative (#283).

  Such a call is inlined: its arguments are evaluated first, in order, then
  its body runs in the caller's clauses, so the body's effects are rolled
  back or kept as the caller's are; the caller needs the callee's declared
  effects, as for any call. Its own `defer:` runs as each value leaves it,
  as a block's does (#283). With named parameters, as at any call: the
  positional arguments, then the named ones as written, then the defaults
  of those omitted, each seeing only the parameters before it (#283); a
  generic one's (or a generic class's method's) type arguments are inferred
  as at a call: from the arguments given, named ones too, then from the
  defaults of those omitted for a type parameter nothing else determines
  (#283).

  An overloaded function may have several values too (#283): a call takes
  the overload its arguments fit, as any call does, and has that
  overload's values, inlined as it would be alone; an overload with one
  value is an ordinary call. Without types where it is inlined, a function
  that calls such an overloaded one is taken to have several values
  whichever overload it reaches, for now.

  A method with several values works the same way (#283): a call
  `R.M(args)` evaluates `R` first, once, then is inlined like a function's,
  with `Self` the receiver, and so is `M(args)` in its class's methods and
  those of the classes below it. A recursive one is taken lazily, and a
  named parameter's default sees the fields. Inlining happens before
  types are checked, so `R.M` has to name that method whatever `R` is:
  such a method's name must be no other member than it and its overrides
  (in classes below the class or interface that declares it), no struct
  field, enumerator or member of a built-in type (`Length`, `Find`,
  `Signal`, …), no top-level name and no parameter or local. An
  interface's method is such a family's root too (#283): a call through
  the interface dispatches on the receiver's class, as for an overridden
  method; an interface's default implementation is the alternative for
  the classes that have none of their own. A generic class's or
  interface's method may be overridden too, the dispatch taking each
  class's type arguments from the receiver's (#283), when each class that
  has it gives the generic one its own type parameters, all of them, as
  `sbox(t) := class(box(t))`; one that fixes or adds type arguments
  (`ibox := class(box(int))`) is refused, for now. A generic
  class's method is a function generic over the class's type parameters,
  their arguments inferred from the receiver where it is inlined, as at a
  call of a generic function (#283), when no class overrides it. A call of an overridden one dispatches on the
  receiver's class as any method call does, adding no choice of its own
  (#314): in a `for`, a value the filters after it reject undoes what came
  before it, the receiver's and the arguments' effects and the earlier
  clauses, unless the implementation reaches a choice of its own. `(super:)M(…)` calls the
  implementation above; a recursive overridden one is computed at the
  call (its implementations call each other through the dispatch), so
  it must be `<computes>`. Such a method is still checked as a member
  (`<final>`, its signature and effects against the one it overrides, an
  abstract one implemented), but an override with several values must
  return the same type as the method it overrides, not a narrower one, for
  now. Since the dispatch is made before types, a call has the effects of
  the method as the class that declares it declares them, whatever the
  receiver's type (an override may declare fewer). A parameter or local of the method named like a member is refused,
  as anywhere in a class.

  A `return` in the branches of an `if` in such a function's body, after
  its choices, gives the value of the alternative it is reached in, and the
  rest of the body is skipped for it (#283). The `if` stays an `if`, with
  no choice added, so what came before it rolls back as without the
  return:

  ```verse
  H():int =
      Y := 1 | 2 | 3
      if (Y = 2):
          return 99
      Y * 10
  # 10, 99, 30
  ```

  A choice may also come after such an `if`, or be in a `return`'s value
  (`if (X < 0) { return 0 }; X | X + 1`, `return 99 | 98`). The `if` still
  picks one branch, with no choice of its own (#314): in a `for`, a value
  the filters after it reject undoes what came before it, the caller's
  clauses too, unless a choice of the program's own came in between.

  ```verse
  dice := class:
      Sides : int
      Roll()<transacts>:int = 1 | Sides
  Main()<transacts>:void =
      D := dice{Sides := 6}
      for (X := D.Roll(), Y := D.Roll()) { Print("{X}{Y}") }   # 11 16 61 66
  ``` The function itself is still checked
  as any function is (types, effects, `<decides>`), with each choice read
  as any of its alternatives.

  A recursive one (that calls itself, directly or not) is not inlined.
  One shaped as a generator is taken lazily (#246): it calls no other
  function with several values, its clauses have no choice, and its last
  expression is a choice, or an `if … else …` whose branches are choices or
  values, each alternative a value with no choice in it or a whole call of
  the function itself. So is a strongly connected group of such functions
  (#283), mutually recursive, each of that shape with its alternatives
  calls of the group's functions (or, as the last expression or a branch,
  one such call), all of one result type, none generic, none with named
  parameters: `Evens(N:int):int = N | Odds(N + 1)` with
  `Odds(N:int):int = Evens(N + 1)`. Its values are taken one at a time, as the place
  that takes them asks for them, in spatial order (depth first), so an
  infinite one works where the first success is taken, and a value never
  reached is never computed. A call evaluates its arguments first; when
  its clauses fail, it has no values, and what its arguments did stays, as
  for a recursive call computed at the call. It may have effects:
  - in a `for`, its clauses run as its values are taken, between the
    iterations, and stay, as a `for` keeps the effects of clauses before a
    choice; what a value does is undone with its iteration when the
    filter rejects it;
  - where the first success is taken (an `if` condition, `first{…}`,
    `option{…}`, `logic{…}`, `not`, the left of `or`), effects are undone as
    the Verse Calculus undoes them: what a value does with that value, and
    what a call's clauses, the conditions of its last `if` and its
    arguments do with all the values that call leads to, when the context
    rejects them all (a tree walk that prints keeps only the path to the
    value taken). When those have effects, the call and the clauses after
    it run as a function of their own, recursive (also in a method, taking
    `Self`; not yet where those clauses call `(super:)` or use `Self` of a
    generic class).

  ```verse
  Upto(A:int, B:int)<transacts><decides>:int =
      A <= B
      Print("visit {A}")
      A | Upto[A + 1, B]
  Nat(N:int)<computes><decides>:int = N | Nat[N + 1]
  Main():void =
      for (X := Upto[1, 2]) { Print("got {X}") }   # visit 1, got 1, visit 2, got 2
      if (X := Nat[0], X * X > 50) then Print("{X}")   # 8
  ```

  The others, if they are `<computes>`, keep no local state (no `var`, no
  `set`), and nothing they may run prints or calls `Err()`, have their
  values computed at the call, all of them, in order, as an array the call
  then takes them from (#235).
  What it may run is followed through its Verse Core code, so through every
  call: the functions it calls, each implementation a method call may
  dispatch to, each function of a function value's type that the program
  uses as a value, the field defaults and `block:` clauses of the classes and
  structs it constructs, the constants it uses, and the defaults of the
  parameters its calls omit. An argument of such a call that fails gives no
  values for that call alone, as a failing clause does.

  Computing all the values first is the same as taking them one by one,
  since nothing it runs has an effect, as long as computing them all stops
  without an error. If it does not stop (infinitely many values), or stops
  the program with an error (an overflow, the recursion limit), so does the
  call, even where only the first success is taken and a value before the
  error would have been it.

  Refused for now: a recursive one that is not a generator and is not
  `<computes>`, or may print or call `Err()`, a generator whose clauses,
  conditions or arguments have effects where the first success is taken
  and the clauses after it call `(super:)` or have a `return` or a `break`
  that leaves them (which would leave the function they run in), in a constructor, a parameter's
  or field's default or a `defer:`, or where the names the clauses after it
  use have type parameters (`Self` of a generic class among them), an
  overloaded one with an overload that calls the function's own name
  (a generic one's type arguments are inferred from the
  arguments where it is inlined, as at a call, named ones too), a recursive
  one with named parameters, a recursive one with a `defer:` of its own, or called by a recursive one (its body a function's, where it would run once), one with a `defer:` after a `return` (which may leave before it is reached), or with an `if`'s branch that has a `defer:` of its own, a `return` before its end and a path that does not return, one with a `return`
  other than in an `if`'s branches, or recursive with a `return`, a method whose name another class or interface
  also has, overridden in a class that fixes or adds a generic class's type arguments, generic, `<suspends>` or using `(super:)`, one used as a function value, and, since its body is inlined where other names may be
  in scope, one whose name is also the name of a parameter, local, field or
  method anywhere in the program, and a call of one where a name its body
  uses from outside is a parameter, local or member of `Self` in scope.
  `Main` never has several values.
- **Precedence.** `|` binds looser than arithmetic and tighter than the
  comparisons: `X = 1 | 2` is `X = (1 | 2)`.

**What is proved, and what is tested.** In Verse Core a choice is
iteration over its alternatives' indices (`Expr.altE`, `Expr.chooseFirst`
and `Expr.firstE` in `Core/Derived.lean`), so no proof or part of the C
runtime changes. Every guarantee in the README's "What is proved" holds of
programs with choices as of any other: one outcome, rollback of failure
contexts, type safety. About choice itself, `Core/Derived.lean` proves
facts about those Core forms, for the first success, as sufficient
conditions:
- If the alternatives before `j` fail, each started from the state at the
  choice (so rolled back), and alternative `j` breaks, the choice breaks
  in the state `j` left (`chooseFirst_brk`).
- If they all fail, it ends with no value (`chooseFirst_none`). The
  enclosing failure context then rolls back its effects (`ite_rollback`).
- `firstE` turns the one into success and the other into failure
  (`firstE_of_brk`, `firstE_of_ok`).

Four things are **tested, not proved**:
- that the elaborator emits these forms as described above, lifting a
  choice out of an expression included (the front end is not verified;
  see DESIGN.md, "Translation validation");
- the reading for `for`;
- the order of values across several choices;
- that the code before a choice runs once.

The tests above check them, and `scripts/fuzz-choice.sh` runs both
implementations against a model of these rules written apart from the
compiler.

## any

`any` is the top type (Book of Verse ch. 11, #138): every value is an
`any`, and `any(X)` makes one explicitly. Where no type is expected, two
types with nothing in common join at `any`: `if (C?) then 42 else "text"`,
`array{15.61, "Message", 3}` (a `[]any`). Classes with two common
supertypes are still an ambiguity, and an expected type still decides
(`X:int = if (C?) then 1 else "a"` is refused).

The order of the branches doesn't matter (#366), up to three levels of
such `if`s nested without an expected type (the depth to which a branch is
elaborated against another's, so nesting stays linear): a later branch is
elaborated against the first's type, and when that gives `any`, or the
first has no type on its own, every branch is tried against a later one's
type. So `if (C?) then false else option{4}` is a `?int`, as
`if (C?) then option{4} else false` is, and so is the choice
`false | option{4}`; `if (C?) then array{} else array{4}` is a `[]int`.

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
  their defers, as it does its branches). They take their places in the
  scheduler's order when the `rush` ends, after the tasks already there. A `return` in such an arm, once the `rush` has ended,
  ends that arm only: the function has gone on, and the value is dropped.
  A `rush` cannot be in a `loop` or `for` body (the Book's rule).
- **`branch`.** The body of a `branch:` runs as a task of its own, at once
  up to its first wait, while the code after it goes on. It shares the
  enclosing function's variables, and it is cancelled (running its active
  `defer:` blocks) when that function exits, by returning, ending or being
  cancelled: after the function's own `defer:` blocks, the last started
  branch (or `rush` arm going on) first, each unwinding whole: what its own
  code started (a `rush` it waits in, the branches it started) is stopped
  first, the same way, then its own `defer:` blocks run (#254). A branch or
  `rush` arm that has ended still owns what it started: those are stopped
  in its place in that order, not by their own start among the function's. A `branch` cannot be in a `loop` or `for` body (the Book's
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
  it unwinds at once, running its `defer:` blocks, or, when the task is
  running (its own code or one of its branches or `rush` losers runs: it
  cancels itself, or a task or branch started while it runs, at any depth,
  cancels it in its first run), when the code that runs waits next, or
  ends; cancelling a task while it unwinds, or awaiting it then, finds it
  cancelled already. Awaiting a cancelled task cancels the task that
  awaits, also in a task's or a branch's first run (and a `Main` that
  awaits one is cancelled, which ends the program). A task asked to be
  cancelled at its next wait that ends before it waits again ends as
  usual; cancelling a task that has ended changes nothing.

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
  after a `Signal` gives that value at once. A `subscribable_event(t)` is an
  event that also calls the functions subscribed to it:
  `E.Subscribe(F)` (with `F` a function or method value of type
  `type{_(:t):void}`) gives a `cancelable`, whose `Cancel()` unsubscribes
  `F`, and `E.Signal(X)` calls each subscribed function in the order they
  subscribed (see [Readings](#readings-openverse-takes)), after waking the
  tasks awaiting `E`, which go on once `Signal` has returned (#210). A
  function subscribed during a `Signal` is first called at the next one; a
  function cancelled during a `Signal`, by one called before it, is not
  called by it. As in the Book (ch. 14, "Transactional Behavior"), a
  `Subscribe` or a `Cancel` in a failure context that fails is undone. A
  `Signal` may be called in a failure context too, which Verse refuses
  (the API reference makes its `Signal` `<no_rollback>`): what the
  functions it calls do is rolled back with the context, as `Print` is.
  A `subscribable_event()` is one without a value: `E.Signal()`,
  `E.Await()`, and functions of type `type{_():void}` to subscribe (#220).
  It is an `event(void)`, but not a `subscribable_event(t)`, whose
  functions take a value.
  The Book marks subscribable events as not yet released in Verse;
  openverse follows the Book's description of them.
- **Arms.** Arms share the enclosing function's variables. An arm is a
  scope of its own, which `break` cannot leave. A `return` in an arm
  returns from the enclosing function: the arm's defers run, then the other
  arms that started are cancelled (last started first), then the defers of
  the scopes around the `sync`, `race` or `rush`. A `sync` or `race` that is
  cancelled from outside (its task cancelled, its function's branch
  stopped) cancels its arms the same way, last started first. A `return` in a `branch`
  is an error, as in a `defer`.
- **Effects.** `<suspends>` and `<decides>` exclude each other. A suspends
  function, `Sleep`, `sync` and `race` can be used only in a suspends
  function, and not in a failure context (an `if` condition, a `for`
  filter, a `case` pattern, a `<decides>` call's arguments) nor in a
  `defer`. A method may be `<suspends>` (an override must be too, and
  only when what it overrides is). Code generic over a class can call one
  that a subclass fixing or repeating its type arguments overrides
  (`int_box := class(box(int))`, `dup(t) := class(pair(t, t))`), under
  the refinement that gives (#142, #171, #209), also
  when the override has type parameters of its own or of its class
  (`ipair(b) := class(pair(int, b))`). A `<suspends>` constructor is not
  supported. `<suspends>` combines with the heap effects
  (`<computes>`, `<reads>`, …): waiting has none.
- **Time.** The schedule is deterministic: a virtual clock counts ticks, 30
  per second, and ticks in which nothing can run are skipped. In each tick,
  `Main` goes on first, then each task in the order they were spawned, then
  again while a task ended, a `Signal` woke a task, or a task was cancelled
  (so that those waiting go on in the same tick). Arms that can go on in the same tick do so in source order. `Sleep(S)`
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
- **Generic functions.** A generic function with a `branch`, a `rush` or a
  `spawn` is compiled once, as any generic function: its tasks are roots
  of the scheduler at its type arguments (#244), and it may call itself at
  ever bigger types (`F(X:t)` calling `F(array{X})`). So is one with a
  spawned dispatch whose receiver or arguments have types that mention its
  type parameters (`spawn{E.Eval()}` on an `expr(t)`), and a generic
  immediate function with a `spawn` (#174, #209).

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
| Order of a choice's values | (not in the Book; the Verse Calculus: spatial) | spatial: the leftmost choice varies slowest, as nested generators do (#208) |
| Code before a choice | (the Verse Calculus is pure) | runs once, also within an expression (the operands before the choice are evaluated first, as written); each alternative runs the code after the choice, from where the choice was reached; in an `if` or `first{}`, one that leads to no success is rolled back (as backtracking does); in a `for`, the choice is a generator, so only an alternative whose own clauses fail is (#208) |
| Precedence of `\|` | (not in the Book) | below `+`, above the comparisons: `X = 1 \| 2` is `X = (1 \| 2)` (#208) |
| `Sleep(0.0)` | "may resume in the same tick" (ch. 14); the API reference: it always yields | always yields: resumes in the next tick (#156) |
| `Sleep(S)` rounding | rounded up to whole ticks (ch. 14) | `Round(30·S)` ticks, at least one: rounding to the nearest keeps `Sleep(0.1)` at 3 ticks despite binary floats (#156) |
| End of a program with tasks | not stated | the program ends when `Main` does; a `Main` that waits with no task able to run is an error (exit 2) (#156) |
| Order of a `subscribable_event`'s functions | not stated (ch. 14's example lists them in subscription order) | subscription order; the tasks awaiting the event are woken first and go on after `Signal` returns (#210) |
| Extent of a `<#>` comment | "everything indented by four spaces on subsequent lines" (§1.1) | the rest of the `<#>` line and every following line indented more than that line, whatever the amount (blank lines included); `<#>` may also follow code on a line |

## Not supported in v1

arithmetic on rationals (see [rational](#rational)), float functions beyond those of [float](#float),
the class features listed under [Classes](#classes), struct methods (Verse structs have none; classes do),
`weak_map`, module paths `using{/Verse.org/…}` (accepted and ignored), overloading beyond [Overloading](#overloading), nested
functions and lambdas (not released in Verse), choice beyond [Choice](#choice) (recursive functions with several values that have effects, other than generators, methods with several values whose name another class shares or that a class fixing a generic class's type arguments overrides; a choice inside a construction whose default runs before it), concurrency beyond [Concurrency](#concurrency), and effect checking
other than `<decides>` and the heap effects (`<converges>` is accepted and
ignored).
