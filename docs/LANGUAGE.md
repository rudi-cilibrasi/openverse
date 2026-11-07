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

## Supported

| Area | Supported | Book |
|---|---|---|
| Comments | `#` to the end of the line, nested `<# … #>`, `<#>` indented comments (the rest of the line and every following line indented more than it; see [Source text](#source-text)) | ch. 0 |
| Literals | `int` (decimal, `0x` hex; must fit in 64 bits), `'c'` `char` (`c` printable ASCII U+0020–U+007E, or an escape), `0oHH` `char` code unit (one or two hex digits, not octal: `0o41` is `'A'`, `0o9` is a tab), strings with escapes and `{expr}` interpolation, `true`, `false` | §1.3–1.7 |
| Types | `int`, `logic`, `char`, `string` (= `[]char`), `[]t`, `?t`, `tuple(…)`, `void` | ch. 2–3 |
| Definitions | top-level functions `F(X:t, …)<effects>:t = body`, top-level constants `C:t = e` / `C := e`; locals `X := e`, `X:t = e`, `var X:t = e`; no shadowing | §3.1–3.4 |
| Mutation | `set X = e`, `set X += e` (`-=`, `*=`), `set A[i] = e` (fails out of range; returns `e`), and paths `set S.F.G = e`, `set A[i][j] op= e`, `set M[k].F = e`: indices and keys evaluated once, left to right, then the new value, then the variable rebuilt; an index out of range or a missing intermediate key fails, while the last key of a path inserts | §3.3, §3.5, §9.3 |
| Blocks | indented (`:`), braced (`{ }`), inline (`then`/`do`), `block:`, `( a; b )` sequences | §2.2–2.4 |
| Operators | `* + -`, unary `-`, comparisons `= <> < <= > >=` (failable, return the left operand, chains check every pair), `and`, `or`, `not`, `?`, `.Length`, `A[i]`, `T(k)` | ch. 4 |
| Failure | failure contexts (`if` conditions, `for` clauses, `option{}`, `logic{}`, `not`, left of `or`, `<decides>` bodies) with rollback of `var` writes **and output** | ch. 8 |
| Control | `if`/`else if`/`else` (all styles, `if:`…`then:`), `for` with `X : array`, `I -> X : array`, `X := a..b`, filters, bindings, several generators (cartesian product), `loop`/`break`, `return`, `case` with literal patterns and `_` | ch. 7 |
| Functions | recursion, mutual recursion, `<decides>` (called with `F[…]`; other functions with `F(…)`), named parameters `?P:t = default` passed as `?P := e` (positional, then named as written, then defaults), other effect specifiers accepted and ignored | ch. 6, 13 |
| Parametric functions | `F(X:t, … where t:type, u:subtype(comparable))`: type parameters in parameter types, the result type and local declarations; type arguments inferred at each call (see [Parametric functions](#parametric-functions)) | Types: where clauses |
| Structs | `name := struct:` with typed fields and defaults, `name{F := e, …}`, `S.F`, `set S.F = e` / `op=`, structural equality (a struct is the tuple of its fields in Verse Core) | ch. 9 |
| Parametric structs | `pair(t:type, u:type) := struct:`, the type `pair(int, string)`, values `pair(int, string){First := 1, Second := "a"}` (or `pair{…}` where the expected type gives the type arguments); see [Parametric structs](#parametric-structs) | ch. 9 |
| Classes | `name := class:` and `name(t:type) := class:` with fields and methods; `class(parent, interface, …)`, `interface`, `<abstract>`, `<override>`, `<final>`, `(super:)`, virtual dispatch, casts `T[X]` and `T(X)`; no `var` fields; see [Classes](#classes) | ch. 10 |
| Enums | `name := enum:` / `enum{A, B}`, `name.A`, equality, `case` that needs no `_` when every value is named (an enumerator is its index in Verse Core) | ch. 9 |
| Maps | `[k]v`, `map{k => v, …}` (a key given twice keeps its last value, at its last position), `M[k]` (fails on a missing key), `set M[k] = v` (insert or update, never fails), `set M[k] op= v` (fails on a missing key), `.Length`, `for (V : M)`, `for (K -> V : M)` in insertion order, order-sensitive equality (a map is the array of its pairs in Verse Core) | §3, §9.3 |
| Array methods | `A.Slice[i, j]`, `A.Slice[i]`, `A.Find[x]`, `A.RemoveElement[i]`, `A.ReplaceElement[i, x]`, `A.Insert[i, B]` (all failable) | §9.1 |
| Built-ins | `Print(s)`, `ToString(x)` (int, char, string), `Floor(X / Y)`, `Ceil(X / Y)`, `Quotient[X, Y]`, `Mod[X, Y]` (Euclidean), `Abs`, `Min`, `Max`, `Err()` | API reference |
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
- **Limits.** Named parameters, a generic `Main`, several constraints on one
  type parameter (also unsupported in the Book), explicit type arguments to
  a generic function, and generic constants are not supported.

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

Classes without `var` fields (#14, #18): fields and methods, parametric
classes, single inheritance, interfaces and virtual dispatch.

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

- **Values.** Without `var` fields an instance cannot change, so reference
  semantics cannot be observed. A class is constructed like a struct
  (`circle{R := 1}`), and `set` cannot reach a class field, not even
  through a path.
- **Methods.** A method `M` of class `c` is a function `c.M` whose first
  parameter is `Self`. In its body, a name that is not a local is looked up
  among the fields, then the methods, inherited ones included. A local or
  parameter with the name of a field or method is an error, and so is a
  method named like a built-in function. Field defaults are elaborated where
  they are defined. `Obj.M(…)` evaluates `Obj` before the arguments.
- **Inheritance.** `c := class(parent, i₁, …)` has at most one class parent
  and any number of interfaces, and `i := interface(j, …)` extends
  interfaces. A class inherits its parent's fields, first, and its methods:
  - `Name<override>:t = e` gives an inherited field a new default; any
    other field with an inherited name is an error;
  - `M<override>(…)` overrides an inherited method with exactly its
    signature. Overriding without `<override>`, or `<override>` that
    overrides nothing, is an error;
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
- **Casts.** `T[X]` is `X` as a `T`, failing unless `X`'s class is below
  `T`. `T(X)` converts to a supertype and cannot fail.
- **Parametric classes.** A method of a parametric class is generic over the
  class's type parameters, then its own. The type arguments come from the
  receiver, and the body is checked once in Verse Core (see
  [Parametric functions](#parametric-functions)).
- **Comparability.** A class or interface is not comparable (Book §4.9), nor
  is a struct or container that holds one.
- **Not yet supported** (each rejected with a message that names its phase
  of #11):
  - `var` fields, `<unique>`, `block:` initialisers, constructor functions,
    and recursive classes, which need references (phase 3);
  - parametric classes in hierarchies;
  - overriding a method with its own type parameters;
  - covariant return types;
  - interface fields;
  - qualified `(i:)M` implementations;
  - named arguments to a method dispatched on the receiver's class;
  - subtyping through `+` on arrays, through tuples and through maps, and an
    array literal of different classes without an expected type.

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
| Extent of a `<#>` comment | "everything indented by four spaces on subsequent lines" (§1.1) | the rest of the `<#>` line and every following line indented more than that line, whatever the amount (blank lines included); `<#>` may also follow code on a line |

## Not supported in v1

`float` and `rational` values (only `Floor(X/Y)` and `Ceil(X/Y)` of ints),
`char32`, classes beyond phase 1 (see [Classes](#classes)), interfaces, open enums, struct methods (Verse structs have none; classes do), `ConcatenateMaps`,
`weak_map`, modules beyond
ignoring `using`, overloading, defaults that refer to earlier parameters, nested
functions, `first`, `defer`, refinement types, concurrency (`spawn`, `sync`,
`race`, `rush`, `branch`, `<suspends>`), `weak_map`, and effect checking for
`<reads>`/`<writes>`/`<computes>`. Comparing arrays with tuples (`array{1,2}
= (1,2)` succeeds in the book) is not supported: arrays and tuples are
different values and compare unequal.
