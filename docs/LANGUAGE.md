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

- The language: [Supported](#supported) · [Source profiles](#source-profiles) · [Source text](#source-text) · [Parametric functions](#parametric-functions) · [Function values](#function-values) · [defer](#defer) · [Overloading](#overloading) · [Parametric structs](#parametric-structs) · [Classes](#classes) · [Mutation, macros, tooling](#mutation-macros-tooling) · [Choice](#choice)
- More types: [any](#any) · [Refinement types](#refinement-types) · [float](#float) · [rational](#rational) · [char32](#char32)
- Programs: [Modules](#modules) · [Programs of several files](#programs-of-several-files) · [Concurrency](#concurrency)
- [Readings openverse takes](#readings-openverse-takes) · [Not supported in v1](#not-supported-in-v1)

## Supported

| Area | Supported | Book |
|---|---|---|
| Comments | `#` to the end of the line, nested `<# … #>`, `<#>` indented comments (the rest of the line and every following line indented more than it; see [Source text](#source-text)) | ch. 0 |
| Literals | `int` (decimal, `0x` hex; must fit in 64 bits), `'c'` `char` (`c` an ASCII character other than a line break, a tab included, or an escape; a non-ASCII one, `'é'`, is a `char32`, Book of Verse ch. 1), `0oHH` `char` code unit (one or two hex digits, not octal: `0o41` is `'A'`, `0o9` is a tab), strings with escapes and `{expr}` interpolation, `true`, `false`, `0uHHHHHH` `char32` (a Unicode scalar value, up to `0u10FFFF`, no surrogates), `float` `1.5`, `2.0e-7`, `1e3`, `12.34f64`, `1234f64` (digits, then a point and digits or an exponent or both, or the suffix `f64`, which may follow either; the nearest double, which must be finite: `2.0e308` is refused; `f32` and `f16` are read and refused as not supported); paths `/Verse.org/Random` parse (in `using{…}`, ignored; as values, refused; see [Source text](#source-text)) | §1.3–1.7 |
| Types | `int`, `logic`, `char`, `char32`, `any` (see [any](#any)), `rational` (see [rational](#rational)), `float` (see [float](#float)), refinement types `type{_X:int where 0 <= _X, _X <= 120}` (see [Refinement types](#refinement-types)), `string` (= `[]char`), `[]t`, `?t`, `tuple(…)`, `void`, function types `type{_(:int)<decides>:int}`, with named parameters `type{_(:int, ?B:int):int}`, and `int->int` (see [Function values](#function-values)); a tuple converts to an array of its elements where an array is expected, and compares with an array as one (`array{1,2} = (1,2)`) | ch. 2–3 |
| Definitions | top-level functions `F(X:t, …)<effects>:t = body`, top-level constants `C:t = e` / `C := e` (definitions on one line, at the top level or in a module, are separated by `;` or `,`: `X:int=0, Y:int=0`; a constant may use one defined after it, but not itself, directly or through other constants); locals `X := e`, `X:t = e`, `var X:t = e`, and a tuple destructured, `(X:int, _, Z:string) = e` (each named element a local of the block, `_` skipping one, `e` evaluated once); no shadowing; no name defined twice in a scope but [overloaded](#overloading) functions; no [reserved name](#reserved-names) | §3.1–3.4 |
| Mutation | `set X = e`, `set X += e` (`-=`, `*=`), `set A[i] = e` (fails out of range; returns `e`), and paths `set S.F.G = e`, `set A[i][j] op= e`, `set M[k].F = e`: indices and keys evaluated once, left to right, then the new value (for `op=`, after the old one is read: `set X += e` is `set X = X + e`), then the variable rebuilt; an index out of range or a missing intermediate key fails, while the last key of a path inserts | §3.3, §3.5, §9.3 |
| Blocks | indented (`:`), braced (`{ }`), inline (`then`/`do`), `.` and an expression on its line wherever `:` or `{…}` may start a body (`if (c). e else. f`, `for (X:Xs). e`, `spawn. F()`, `loop. break`; also `option`, `logic`, and `array` and `map`, whose `:` blocks separate their items by `,`, `;` or new lines: `array:` and the lines `1`, `2`; in braces an array's elements are separated by commas, or by `;` and new lines, not both: `array{1; 2; 3}`), `block:`, `( a; b )` sequences, also as an argument (`F(Log(); 42)` passes 42) and as a `case`'s value (`case(a; b)`); `;` separates the items of a block and may end a line or a braced block (`{1; 2;}` is `{1; 2}`) (the next item then follows the line rules, so a class's last field may end in `;`); a body after `:` may be empty wherever one may be written, as `{}` may (`class:`, `struct:`, `then:`, … whose next line is no deeper than the construct, or nothing follows); a function's or method's braced body may put its `{` on the next line, at the definition's column; a value after `=`, `:=`, `set … =` or a `case` arm's `=>` that starts a later line, deeper, is the indented block of those lines (`Value :=` and the lines `1`, `2`, `3` is `3`), as a function's body is | §2.2–2.4 |
| Operators | `* + -`, unary `-`, comparisons `= <> < <= > >=` (failable, return the left operand, chains check every pair), `and`, `or`, `not` (below the comparisons, above `and`: `not X = Y` is `not (X = Y)`), `?`, `.Length`, `A[i]`, `T(k)` | ch. 4 |
| Failure | failure contexts (`if` conditions, `for` clauses, `option{}`, `logic{}`, `not`, left of `or`, `<decides>` bodies) with rollback of `var` writes **and output**; an `if` condition, `logic{…}` and the operand of `not` must be able to fail (the Book's tests refuse `not` of one that cannot; the left of `or` may not, as in the Book's own `(set Map[I] = I) or Err()`) | ch. 8 |
| Control | `if`/`else if`/`else` (all styles: the conditions in `(…)`, followed by a body or `then`; or as `{…}`, `:` and a block, or `.` and an expression, followed by `then` and a branch, or by nothing, which is the clause macro `if{c}` (see [Mutation, macros, tooling](#mutation-macros-tooling)): `if:`…`then:`, `if:`…`else:`, `if. c then. a else. b`; `for` likewise, with `do`), `for` with `X : array`, `I -> X : array`, `X := a..b`, filters, bindings, several generators (cartesian product), and with none, failable clauses that run the body at most once (clauses of literals only, `for(X := array{1, 2})`, are refused: `X : array{1, 2}` iterates), `loop`/`break`, `return` (in a function's body: not in a constant's value or a field's default, which no function encloses), `case` with literal patterns and `_` (an arm after `_`, or with an earlier arm's pattern, is never reached and refused, ch. 9) | ch. 7 |
| Choice | `a \| b \| …` with several values in spatial order, in a clause of an `if` condition, `first{…}`, `option{…}`, `logic{…}`, `not` or `or` (the first success) or of a `for` (all of them), also inside expressions (`(1 \| 2) + (10 \| 20)`, `X = 1 \| 2`, `X > 0 and (1 \| 2)`, `M? or (1 \| 2)`); see [Choice](#choice) (#208) | (the Verse Calculus) |
| Functions | a parameter may be unnamed, `F(:int):void = {}`, as in function types (the body cannot name it; so may a parametric type's, `t(:type) := class{}`); a parameter may destructure a tuple, `Func(A:int, (B:int, C:int), D:int)`, to any depth: it is a parameter of the tuple type whose names the body sees (see [the rules](research/tuple-parameters.md); named parameters inside such a group are not supported); a tuple argument expands into parameters (`Describe(MyTuple)`); positional arguments pack into a single tuple parameter, including `tuple()` and singleton tuples; several arguments make a single array parameter (`Sum(1, 2, 3)`), including generic, overloaded, method and spawned calls (#134, #140, #501; nested fields retain their shape, and empty/singleton arrays use explicit array values); recursion, mutual recursion, `<decides>` (called with `F[…]`; other functions with `F(…)`), named parameters `?P:t = default` passed as `?P := e` (positional, then named as written, then defaults; a default may use the parameters before it, and a method's default the method's fields; a call dispatched to an override evaluates that override's own default for an omitted argument; a default is evaluated at the call, its effects counting as the caller's, and cannot return, break or use itself), the heap effects `<computes>`, `<reads>`, `<writes>`, `<allocates>`, `<transacts>` (checked, see [Classes](#classes)), unsupported effect contracts are diagnosed before lowering (see [Effect contracts](#effect-contracts)) | ch. 6, 13 |
| Parametric functions | `F(X:t, … where t:type, u:subtype(comparable))`: type parameters in parameter types, the result type and local declarations; type arguments inferred at each call (see [Parametric functions](#parametric-functions)) | Types: where clauses |
| Structs | `name := struct:` with typed fields and defaults, `name{F := e, …}` (each field given at most once, evaluated in declaration order; separated by commas, or by `;` and new lines, not both; or as an indented block after `name:`, an archetype block; the type may be parenthesized, `(pair(int)){…}`), `S.F`, `set S.F = e` / `op=`, structural equality (a struct is the tuple of its fields in Verse Core) | ch. 9 |
| Parametric structs | `pair(t:type, u:type) := struct:`, the type `pair(int, string)`, values `pair(int, string){First := 1, Second := "a"}` (or `pair{…}` where the expected type gives the type arguments); see [Parametric structs](#parametric-structs) | ch. 9 |
| Classes | `name := class:` and `name(t:type) := class:` with fields and methods; `class(parent, interface, …)` (`class()` has none, as `class`; a type `t()` or value `t(){…}` with no type arguments is `t`, `t{…}`), `interface`, `<abstract>`, `<override>`, `<final>`, `(super:)`, virtual dispatch, casts `T[X]` and `T(X)`; no `var` fields; see [Classes](#classes) | ch. 10 |
| Enums | `name := enum:` / `enum{A, B}`, `name.A`, equality, `case` that needs no `_` when every value is named (an enumerator is its index in Verse Core); `enum<open>` may gain values, so a `case` on one needs `_` or a failure context (`<closed>` is the default) | ch. 9 |
| Maps | `[k]v`, `map{k => v, …}` (a key given twice keeps its last value, at its last position), `M[k]` (fails on a missing key), `set M[k] = v` (insert or update, never fails), `set M[k] op= v` (fails on a missing key), `.Length`, `for (V : M)`, `for (K -> V : M)` in insertion order, `ConcatenateMaps(M1, M2, …)` (a later map's value wins for a key, which keeps its first position), order-sensitive equality (a map is the array of its pairs in Verse Core) | §3, §9.3 |
| Array methods | (also of a tuple of one element type, which is an array where one is expected: `('a', 'b', 'c').Slice[1]`) `A.Slice[i, j]`, `A.Slice[i]`, `A.Find[x]`, `A.RemoveElement[i]`, `A.RemoveFirstElement[x]`, `A.Remove[i, j]` (half-open), `A.ReplaceElement[i, x]`, `A.ReplaceFirstElement[x, y]`, `A.Insert[i, B]`, `A.Last[]`, `A.Last[n]` (the element n before the last) (all failable); `A.RemoveAllElements(x)`, `A.ReplaceAllElements(x, y)`, `A.ReplaceAll(Pattern, Replacement)` (contiguous subarrays, left to right, not overlapping; an empty pattern changes nothing), `Concatenate(A, B, …)` or `Concatenate(Arrays)` (#150) (never failing) | §9.1 |
| Built-ins | `Print(s)`, `ToString(x)` (int, float, char, string), `Floor[F]`, `Ceil[F]`, `Round[F]`, `Int[F]` (of a float, failable), `Floor(R)`, `Ceil(R)` (of a rational or an int, never failing; `Floor(X / Y)` fails when `Y = 0`, as `X / Y` does), `Quotient[X, Y]`, `Mod[X, Y]` (Euclidean), `Abs`, `Min`, `Max`, `Clamp(Val, A, B)` (the median of the three, of ints or of floats, NaN ordering above +Inf), `Sgn(X)` (-1, 0 or 1 of an int or a float, NaN of NaN), `F.IsFinite[]` (as `IsFinite[F]`), `Err()`; the conversions of chars and code points as methods (see [char32](#char32)): `C.ToCodeUnit()`, `C.ToAsciiChar32[]` of a char, `C.ToCodePoint()`, `C.ToAsciiString()` of a char32, `N.ToChar[]`, `N.ToChar32[]` of an int | API reference |
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
  Columns count characters, so a tab is one column. The first token of a
  line has the line's indentation as its column, also after a block
  comment: `<#C0#>f():void = 3` is a definition at column 0.
- `<#>` starts an indented comment: the rest of its line, then every
  following line indented more than the line that contains the `<#>` (more
  leading tabs and spaces, counted as columns like the offside rule does),
  with blank lines inside included. It ends before the first non-blank line
  indented no more than that line. `<#` opens a nested block comment only
  when the next character is not `>`; inside a block comment, `<#>` opens
  nothing, so its `#>` closes the block comment.
- The markers of block comments count inside a `#` comment and a `<#>`
  comment too, as in the Book's tests of the lexical grammar
  (`TimSyntax.versetest`): there `<#` opens a nested block comment, which
  may end on a later line (the `#` comment then goes on to the end of that
  line), and a `#>` that closes no block comment is an error, anywhere.
- A block comment inside a string literal is removed from it (ch. 1: "The
  compiler removes comments from strings": `"abc<#comment#>def"` is
  `"abcdef"`); `\<\#` is the text `<#`, and `<#>` and `#` are text there.
- A `0o` char literal is `0o` and one or two hex digits, not followed by a
  letter, digit or `_`; anything else (`0o`, `0o123`, `0o4g`) is an error.
  Its value is that UTF-8 code unit, so `0oC3` is a valid `char` although it
  is not ASCII.
- A path literal (Book of Verse ch. 1, "Path Literals"; ch. 16, "Paths") is
  `/` and a label, then optionally `@` and a label, then segments `/X`: a
  label is ASCII letters, digits, `.` and `-`, starting with a letter or
  digit; a segment is an identifier, which may end in a quoted part
  (`/a/b'+'`) and may be preceded by a qualifier (`/a/(/b:)c`). A path
  cannot be followed by `/` or `@` (`/a/1b`, `/a@b@c` are errors). A `/`
  starts a path only where an operand starts and before a letter or digit:
  after a name other than a keyword, a literal or a closing bracket, `/`
  divides, so `X/2`, `F()/2` and `X /2` are divisions and `/a/b-c` is the
  path `/a/b` minus `c`. A path parses wherever an expression may start
  and in `using{…}`, which accepts and ignores it; as a value it is
  refused ("not supported": openverse has no module values).

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

### Reserved names

No definition, at any scope (a module's or a class's member, a function's
parameter or local, a type parameter, a field), may take one of these names
(`reservedNames` in `Front/Syntax.lean`): `_`, which the Book reserves
(ch. 1: "The single underscore `_` is reserved and cannot be used as an
identifier"); the built-in names `Self`, `subtype`, `castable_subtype` and
`local`; and the names the Book's tests reserve for the future
(`Tests/NamesReservedForFuture.versetest`; the Book's prose gives no list):
`abstracts`, `as`, `assert`, `backslash`, `bag`, `char8`, `char16`,
`collection`, `contravariant`, `covariant`, `element`, `embargo`, `ensure`,
`fails`, `find`, `first`, `float16`, `float32`, `float64`, `float128`,
`fold`, `function`, `given`, `guard`, `implies`, `instance`, `int8`,
`int16`, `int32`, `int64`, `interacts`, `introspects`, `invariant`,
`iterates`, `known`, `last`, `let`, `markup`, `nat`, `nat8`, `nat16`,
`nat32`, `nat64`, `over`, `permutation`, `provided`, `random`, `repeat`,
`sequence`, `string8`, `string16`, `string32`, `subclass`, `succeeds`,
`syntax`, `throws`, `trait`, `truth`, `try`, `union`, `using`, `verify`,
`when`, `while`. openverse reads `first`, `assert` and `let` as macros
before `{` or `(`, and `using` is a keyword. The function type
`type{_(:int):int}` writes `_` as no definition's name, and stays allowed.

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
- **Argument packing** (#501). A bare type parameter accepts multiple positional
  values as a tuple, or as an array when the expected result determines that
  type (`R:[]int=Id(1,2)`). Generic array formals use ordinary array inference,
  including class joins. Grouped contextual values may take their types from
  later named arguments. A lone scalar remains a scalar for a bare type
  parameter; it is not implicitly converted to a singleton array.
- **Limits.** A generic `Main`, several constraints on one type parameter
  (also unsupported in the Book), explicit type arguments to a generic
  function, and generic constants are not supported.

## Effect contracts

The supported effect vocabulary is `computes`, `reads`, `writes`, `allocates`,
`transacts`, `decides` and `suspends`. Function declarations and function types
reject duplicate or contradictory effects, and reject unknown execution
specifiers before lowering can erase them (#494). They also reject a redundant
one, as classes, interfaces and structs do: `<transacts>` implies `<reads>`,
`<writes>` and `<allocates>` (ch. 13), so `<transacts><allocates>` is refused.

`predicts` and `converges` are explicitly unsupported, including on abstract
signatures and function types. The pinned Book calls prediction unreleased
and divergence checking planned; this does not establish their availability
in every released engine. OpenVerse does not implement predicting call
propagation or explicit function termination contracts. Ordinary recursion
and loops remain available outside the initializer admission boundary;
`computes` and execution fuel do not prove termination.

Source `native`/`native_callable` tags cannot create trusted external bindings.
Explicit internal/implicit effect spellings (`no_rollback`, `dictates`,
`diverges`, `succeeds`, `fails`) and obsolete `varies` are rejected.
Transactional output/events retain their documented OpenVerse policy (#495).

Class/interface/struct heap construction budgets are enforced on definitions
and callers (#508). No heap annotation means `transacts`; `computes` permits
none; `reads`, `writes` and `allocates` permit those named. A subtype must
include its parent types' construction budgets. Data types cannot declare
`decides` or `suspends`. Effects on fields are refused; declaration/access
metadata remains separate. Field defaults also have an independent convergence
admission boundary (#511). Ordinary source function calls are refused there,
including calls through constants, methods and function values, even in unused
definitions. Effectful object construction retains the Book's exception.
Finite primitives, failure, finite `for` expressions and `first` searches whose
generated loops cannot repeat remain available. Unknown loops and recursive
compiler-helper call graphs are refused. This checks admission, not a general
termination theorem for construction blocks or native primitives.

`--extended-defaults` on `run`, `emit`, `check` or `core` explicitly retains
OpenVerse's extended computed defaults, including ordinary helper/callback and
spawn defaults. It makes no convergence assertion; heap, failure, suspension,
source-profile and Core checks still apply. Compiler clients use
`Options.extendedDefaults := true` (or the final compatibility argument of
`compileWith`/`compileTops`). Existing extension fixtures select this option
explicitly. The
[effect inventory](research/effect-conformance.md) records the implemented,
partial and rejected contracts, source/release evidence, regression links and
the native/proof boundary. Admission covers every loaded definition, defaults,
nested types and entry expressions, in both source profiles.

### Where specifiers go

The specifiers that say what a declaration is may be written only where it
can be that (`specifierPlaces` in `Front/EffectPolicy.lean`, the one table
of them; the Book's tests `Tests/Attributes/` and `Castable.versetest`):

| specifier | on | requires |
|---|---|---|
| `<abstract>` | a class (ch. 10; not a method, a field, an interface or a struct) | not `<concrete>` too |
| `<concrete>` | a class or a struct | a default for every field, inherited ones and an interface's included (ch. 10, "Concrete") |
| `<final>` | a class, a method or a field (not an interface, a struct, a module's function) | a method's body, a field's value; no class below overrides a `<final>` field and no construction gives it a value |
| `<final_super>` | a class (not supported yet, #11) | |
| `<final_super_base>` | a class or an interface | a class right below it is `<final_super>` |
| `<castable>` | a class or an interface | no type parameters, nor in a class or interface below it |
| `<unique>` | a class or an interface | |
| `<persistable>` | a class (not supported yet) or a struct | a struct's: no type parameters, and fields that persist: not `any`, a rational, a function, an interface, a class or a struct that is not `<persistable>` (ch. 17; every enum is taken to persist, as openverse does not keep an enum's `<persistable>`) |
| `<override>` | a method or a field | |

Anywhere else, on a definition's name (`c<castable> := class{}`) or after the
keyword of another kind (`interface<abstract>`, `struct<final>`), each is
refused. Enums take `<open>`, `<closed>` and `<persistable>`; access
specifiers are accepted where the parser takes them (see
[Readings](#readings-openverse-takes)), and effects are the subject of the
rest of this section.

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
  below `rational` and a class below the classes above it. A method whose
  signature is fixed by its receiver does too (#209, #231), including a
  generic receiver and an open expected type in generic code:
  `Obj.Describe` is a `type{_(:dog):string}`, holding `Obj`, evaluated when
  the value is made. The receiver's class arguments remain fixed; argument
  and result conversions use the ordinary call rules. And a
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
- A generic function is a value where the expected function type determines
  all its type arguments. This includes an open type in generic code:
  `F:type{_(:t):t} = Identity`. The value retains those arguments and their
  witnesses after the creating function returns. Repeated and compound
  parameter/result types, comparable bounds, failure and suspension are
  supported (#209). Open expected types can also pack several parameters
  into one tuple or expand a tuple parameter into separate parameters.
  A bare generic parameter can instantiate to the tuple of the target
  parameters. Empty and single-element tuples work on these paths too.
  Comparable arguments may also be unique classes or comparable value
  structs. With no determining expected
  type, a polymorphic identifier remains insufficient (`Map(Xs, Identity)`
  cannot itself determine `Map`'s unknown result parameter).
  Other arguments can determine it first (`Apply(Identity, X)` when `Apply`
  takes `type{_(:t):t}` and `t`), including inlined choice calls, recursive
  producer calls and generic methods. Arguments still run in written order;
  named arguments run as written before omitted defaults. A local, field or
  visible method keeps its meaning when a generic top-level function has
  the same name.
- A bound method's class parameters may repeat, occur inside compound
  parameter/result types, or be absent from its function signature (#209).
  The captured receiver retains their types and hidden witnesses. This
  includes generic callers, interface views/defaults, overrides and
  suspending methods. The receiver is evaluated once when the value is
  created; later calls observe that receiver's current fields.
  For example, `box(t).Pair(X:rational):tuple(t,int)` can be bound as a
  `type{_(:int):tuple(t,rational)}`. The adapter retains the receiver's
  parameters and bounds, converts the argument before the call and the
  result after it. Tuple packing/expansion can be combined with these
  conversions. Effects and failure/suspension requirements still apply.
- A method with its own type parameters can be used at an expected function
  type that determines one instance and satisfies its bounds (#209). The
  receiver fixes the class arguments; the expected type fixes the method
  arguments. The value retains both, including after its creator returns.
  Other arguments of a call can determine the expected type:
  `Apply(B.Same, X)` works when `Apply` expects `type{_(:t):t}` and `t`.
  This includes unqualified methods inside their class, compound receiver
  expressions, choices, tuple adapters and later named arguments. The
  receiver runs once in written argument order, before later arguments and
  omitted defaults. Fields and ordinary method values can still determine
  the call's type arguments themselves.
  Variance does not select an instance of independent method parameters;
  their declared types must match the determining expected type.
  With no determining expected type, the method cannot be bound as a value.
- Bound methods also pack and expand tuples at an expected function type,
  including open types in generic code (#209). For example, a method
  `Pair(X:a,Y:b):tuple(a,b)` can be a `type{_(:tuple(a,b)):tuple(a,b)}`.
  A bare method parameter may stand for the whole tuple, whether its type
  comes from the receiver or the method's own type parameters. The
  receiver's arguments remain fixed; tuple adaptation cannot change them.
  Empty and single-element tuples, comparable bounds, interface defaults,
  overrides, failure and suspension use the same captured receiver and
  argument order as ordinary calls. Without an expected function type,
  a method value keeps its declared shape.
- **Named parameters** (#503). A function type may name parameters after
  its positional ones: `type{_(:string, ?Color:string):string}`. The names
  are part of the type and match by name, in any order; a positional
  parameter's name is not. `?N:t = e` in a type lets a caller of the value
  omit `N`. As the Book says, `e` is not part of the type, and it never
  runs; it is checked at `N`'s type, with literals and top-level names only
  (a local, a parameter or a type parameter there is refused). A function, or a method bound to its receiver, is a value of a
  function type with the same positional parameters when the type's names
  are among its own, it has a default for each one the type leaves out, and
  it has a default for each one the type lets callers omit. So
  `Log(Message:string, ?Level:int=1, ?Color:string="white")` is a
  `type{_(:string):string}`, a `type{_(:string, ?Color:string):string}` and
  its own type, `type{_(:string, ?Color:string = …, ?Level:int = …):string}`,
  which `F := Log` has. A call through a value gives its positional
  arguments, then named ones: every one its type requires, and only ones it
  has. The explicit arguments run as written; then each omitted default runs
  once, at the call, in declaration order and in the function's scope. A
  bound method's defaults read the receiver's fields as they are then, and
  are its dynamic class's; an override that gives a named parameter a
  default is, from a receiver of its class, a value of the types that leave
  that parameter out. A value converts to the function types above its
  type: `type{_(?A:int = …):int}` is below `type{_(?A:int):int}` and below
  `type{_():int}`. Generic functions and methods, effects, failure and
  rollback, suspension, variance and escaping values work as for other
  function values. A parameter may also be written as a signature, as the
  Book's examples do: `Map(Items:[]t, F(:t)<transacts>:u where t:type,
  u:type)`, `?Say():string = Hello`, also among a function type's own
  parameters: `A(F(:int):int, X:int):int`. Not supported: a function whose named
  parameter has its own name (`F(?F:int)`) as a value; named parameters
  inside a tuple parameter, and tuples with named elements. See the
  [pinned rules](research/named-function-values.md).
- A built-in function of one signature is a function like any other: named
  as a value (`CheckSpecials[Sin, NaN, NaN]`, as the Book's tests write), it
  is a value of its type and effects: `Sqrt`, `Exp`, `Ln`, `Sin`, `Cos`,
  `Tan`, `ArcSin`, `ArcCos`, `Pow`, `Log` (`<computes>`), `Sinh`, `Cosh`,
  `Tanh`, `ArSinh`, `ArCosh`, `ArTanh`, `Lerp` (`<reads>`), `IsFinite`,
  `Round`, `Int` (`<computes><decides>`). The program gets an ordinary
  definition of the built-in, which calls it, unless it defines or binds
  that name itself. The others are no values: overloaded (`Abs`, `Min`,
  `Max`, `Floor`, `Ceil`, `ArcTan`, `Clamp`, `Sgn`, `ToString`), generic
  (`Concatenate`, `ConcatenateMaps`) or names a program cannot define
  (`Quotient`, `Mod`, `Print`, `Err`).
- Overloaded functions and methods cannot be used as values (Book of Verse
  ch. 6, "Capture"), with or without named parameters. Local function
  declarations and lambda expressions are unsupported. The pinned Book marks nested functions unreleased and arrow
  lambdas unsupported; this is not a versioned UEFN compatibility result.
  See the [closure design and release evidence](research/closure-design.md)
  for the proposed capture/lifetime rules and implementation gates.

## defer

`defer:` followed by a block runs that block when its scope exits (Book of
Verse ch. 7): at the scope's end, after its value is computed, or on a
`return` or `break` that leaves it. Several run last registered first. A
scope that fails runs none, since its effects are rolled back. A `defer:`
block cannot be empty, fail, `return`, or `break` out of itself, and it is a
statement, not a value: code follows it in its block, whose value is the
last expression's (ch. 7: it "cannot be used in positions where a value is
expected"), so a block cannot end with one, nor an `if`'s or a `for`'s
clauses, and it is no operand (`A and defer{…}`). Lowering: the deferred block is placed after the
rest of its scope, and before each `return` (after its value) and `break`
that leaves it.

A `break` in a `for` filter leaves the enclosing source `loop`, including
when the values come from lazy recursive producers. Internal producer and
suspension loops forward it after its cleanup has run. Breaks in a body's
own `loop` stay local; a `for` body itself is not a break target.
Shared continuations carry clause breaks back to the caller: the filter's
writes commit before source-loop cleanup runs, including through refining
casts. A new local loop keeps its own target even inside a lifted branch.
So does a `break` in the clauses of an `if` condition or `first{…}` that
has a choice ([Choice](#choice), #283): the loop that takes their first
success forwards it, and so does the function of their own that clauses
after a composed choice or an effectful lazy generator run in.

## Overloading

Several functions may share a name when no call could fit two of them (Book of
Verse ch. 6): `Describe(X:int)`, `Describe(S:string)`, `Describe(X:int, Y:int)`.
Nothing else shares a name in one scope (the top level or a module): two
classes, interfaces, structs, enums or constants of one name, or one of them
and a function (`c := class{}` with `c(I:int):c`, which the Book's tests
refuse as "overloading a class"), are a name defined twice. A local cannot
take an overloaded function's name either.
- **Distinct overloads.** Overloads take different numbers of parameters, or
  disjoint types at some position. A single tuple parameter and the same
  flattened positional types are compared element by element: the same
  domains overlap, while a disjoint position distinguishes the overloads.
  The comparison also includes a tuple containing the positional inputs.
  Thus `int` overlaps `tuple(tuple(int))` and `[]int`: a `tuple(int)`
  argument can unpack for the scalar, wrap for the nested tuple, or convert
  to the array. This does not implicitly turn a scalar into an array.
  See the [complete tuple/container table](research/overloading-conformance.md#tuplecontainer-rules).
- **Overlapping types:** `void`, a type parameter, two array, map or option
  types (they share the empty one), an array, option or `logic` with
  another (`false` is each), and a
  class or interface with an interface or a class above or below it (but a
  `<final>` class and an interface it does not implement are disjoint, and
  so are one parametric class's instances at disjoint type arguments). Function
  types overlap regardless of their signatures or effects. A pair that overlaps is refused where the later
  one is defined.
- **Tuples and containers** (#500). A tuple and an array are distinct if
  any tuple element is distinct from the array element. A nonempty tuple
  and a map are distinct if the map key is distinct from `int`; a nonempty
  tuple and an option are distinct if the option element is distinct from
  `int`. Empty tuples retain their container overlap. Function types cannot
  distinguish overloads from arrays or maps, regardless of signature or
  effects. This does not introduce container/function conversions.
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
  its type arguments as for any generic call. Named parameters and defaults
  work in generic overloads too.
- **Methods.** A class or interface may declare a method with several
  parameter lists, and a subclass may override one overload (with its
  list) and add others. A call takes the overload visible at the
  receiver's type that its arguments fit, then dispatches as usual; the
  overloads a class sees must be distinct. Each list is a method of its
  own (`M$ovN`, up to the names of type parameters).
- **Several values** (#283). An overload of a function or a method may have
  several values where another has one (see [Choice](#choice), "Functions
  with several values"): a call takes the overload its arguments fit and
  has its values, so a caller that reaches only overloads with one value
  has one.
- **Qualified implementations** (#125). `(i:)M<override>(…)` implements
  the overload of `i`'s `M` with its parameter list (as an override takes
  its method's), and `X.(i:)M(…)` picks among `i`'s overloads.
- **Constructors.** Constructor names may overload, including generic
  constructors, defaults and delegation. The arguments select one overload.
- **Entry point.** `Main` must have one definition under the OpenVerse CLI's
  entry-point policy. This is separate from ordinary Verse overload rules.
- **Measured gaps.** The [pinned conformance audit](research/overloading-conformance.md)
  records reproducers, diagnostics, source rules and regression links:
  - ordinary calls do not pack arguments into an explicit or generic tuple
    parameter, and generic array packing is incomplete (#501). A tuple
    argument that does not fit a one-argument overload can expand into a
    different overload's positional parameters; its receiver and producer
    are evaluated once, before named arguments and defaults;
  - generic upper bounds other than `type` and `subtype(comparable)` are
    unsupported (#502).

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
  clause of a failure context, `D := T[X]` (or `T[X]` alone) types the
  code after it in its failure context under the refinement, where the
  code's type parameters are unified as `T`'s type arguments say (written
  types included), and so the branch of the `if` whose condition it is in:

  ```verse
  Eval(E:expr(t) where t:type):t =
      if (L := lit[E]) then L.V                         # t = int here
      else if (A := add[E]) then Eval(A.L) + Eval(A.R)  # t = int here
      else Err()
  ```

  It may be a clause of any failure context: a statement of a `<decides>`
  body, or of a block in a failure context; a clause of `option{…}`,
  `logic{…}` or `first{…}`; the operand of `not`, or of `and` or `or`; a
  clause of an `if`'s condition or of a `for`. Inside such a clause, in an
  operand it evaluates in order (`dup[P].C > 3`, `F(dup[P])`), it is lifted
  out to be a clause of its own first, as a choice there is: the operands
  evaluated before it are bound first, so they still run before it. A
  branch of an `if` in a failure context is in it too: one written as an
  expression with such a cast in it (`if (N > 0) then dup[P].C else 0`) is
  the block of it, where the cast is a clause, so it runs only when that
  branch does. The
  rest of its failure context is its branch: `pre; D := T[X]; rest` is
  `pre; if (D := T[X]) then {rest} else fail`, so its failure, or the
  rest's, undoes what `pre` did, output included, as any failure
  context's does:

  ```verse
  AsLit(E:expr(t) where t:type)<decides>:t =
      L := lit[E]
      L.V                                     # t = int here
  First(H:cell, P:pair(a, b) where a:type, b:type)<transacts>:?b =
      option{set H.N += 1; D := dup[P]; D.A}  # undone when P is no dup
  ```

  In an `if`'s condition, and in a `for`'s clauses, the names reach the
  branch, or the body, which runs outside the failure context. In an `if`,
  when the clauses before the cast print nothing, change no object and
  call nothing (always, when it is the first), so that its failure has
  nothing of theirs to undo, the branch is part of the cast's: `if (N :=
  Ns[0], N > 0, D := dup[P])` is `if (N := Ns[0], N > 0) then (if (D :=
  dup[P]) …)`, the `else` the same in both. Otherwise, and in a `for`, the
  cast takes the clauses after it, up to the `for`'s next generator, as
  its branch in a clause of its own, and the branch or the body, when it
  uses the cast's name or names
  those clauses bind, casts the object again, which succeeds (an object's
  class does not change), so that it is typed under the refinement too, as
  it does each later cast among those clauses whose name it uses, from that
  cast's object (bound to a name first, when computed there). An object
  that may name type arguments a cast opens (the first, when it opens, or
  another among them) is read again instead, after the cast whose name it
  reads, when it is read by fields that are no `var`s from that cast's
  name (#250): `if (Print("x"), P := pairE[E], L := lit[P.L], R :=
  txt[P.R]) then (L.V, R.S)` gives a `t` that is `tuple(a', b')` with `a'
  = int` and `b' = string` (an object's fields that are no `var`s do not
  change, so `P.L` is the same object there). Otherwise the branch has the
  later cast's name, with the type it has there, but not its refinement.
  `if (Print("x"), D := dup[P], Y := D.A) then option{Y}` prints `x` only
  when `P` is a `dup`, and its branch has `D` and `Y` with `b = a`. A
  `for`'s clause past that generator that uses the cast's name casts the
  object again there too, where it uses it: a generator's source, a
  binding's value (so it still binds its name), a range's bounds, each
  alternative of a choice, or else the clause as a whole (`for (P : Ps, D
  := dup[P], Y : D.Items, Y > D.C)`); and so does the body when it uses the
  names those clauses bind.

  A cast can also open type arguments the object's type has no names for
  (#250): `if (P := pairE[E]) then (Eval(P.L), Eval(P.R))`, for
  `E:expr(t)`, types the branch with `t = tuple(a', b')`, where `a'` and
  `b'` are `pairE`'s `a` and `b`, unknown but fixed for the branch; their
  values, which the branch's own generic calls at them need, come from the
  object, which holds them in hidden fields as #209's existential classes'
  objects do. A cast to an interface opens its type arguments too, and so
  does a cast to a class or interface beside the object's type, neither
  above nor below it (#53, #351): `c2[C]`, for `C:container(u)` and `c2(t)
  := interface(container([]t))`, types the branch with `u = []t'`, and
  `i1[I]`, for `I:i2(u)`, with `i1`'s type arguments related to `I`'s as
  the classes and interfaces above both say (`t' = u` when `i1(t)` and
  `i2(t)` both extend `base(t)`), and opened otherwise (`i1(t')`,
  whatever the classes below both give `i1`): it succeeds when the
  object's class is below `i1`, as a cast between any class and interface
  types does (Book of Verse ch. 10, "Castable"). An interface has
  no hidden fields, so such a cast tests each class below both, the
  topmost of its class chain there, as a cast to it, whose branch calls the
  function the cast's branch is made into, with the values of `T`'s type
  arguments that class gives. The value of what follows such a cast in its failure
  context, and the names it binds that a branch or body uses, cannot be of
  a type that names an opened one. An opened parameter is as comparable as the one it stands
  for, and also when comparability of a refined type requires that component
  (`t:subtype(comparable)` refined to `tuple(a', b')`). A unique reference
  such as `holder(a')` is comparable independently of `a'`, so it supplies
  no bound on `a'`.

  A successful test of a class with stronger `subtype(comparable)` bounds
  also makes those bounds available in the branch, including when no type
  equality changes. For example, testing `P:root(t)` against a subclass
  `tight(t:subtype(comparable))` permits comparisons of `P`'s `t` fields
  and captured `t` values there. The same bounds are available within a
  selected scalar or multiple-value override. They do not escape to the
  `else`, following code, or an array collected from a possibly empty
  producer.

  The branch is compiled as a function of its own, generic over the
  enclosing function's type parameters, that takes the object (as `D`) and
  the locals the branch uses, at their refined types; the cast becomes a
  dispatch to it, which Verse Core types as it types a refined method call
  (`Typed.dispatch`), so nothing is assumed in Verse Core. In a
  `<suspends>` function the branch and the `else` may suspend (#243): the
  branch's function is then `<suspends>`, and the `if` a suspends call of
  it, cancelled as any (its `defer:`s, then the caller's). A `branch` or
  continuing `rush` arm started there belongs to the enclosing source
  function (#419): it can outlive the cast and is stopped when that source
  function exits, after its own defers, in the documented task cleanup
  order. The cast's lexical defers still run when the cast finishes.
  The existing restrictions on task starts in loop/for bodies apply
  through lifted branches too. In a
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
  for that (written, given by where it is, the `else`'s, or the branch's
  own when the `else` gives none, as `Err()` or a failure context's
  failure does) unless the branch always returns or breaks. In a method, the branch names `Self`'s
  fields and methods as anywhere in the method (its function takes `Self`
  too), and its `(super:)M(…)` calls the implementation the method's class
  inherits, as anywhere in the method (#243), including overloads selected
  by the arguments under the refinement. Refining casts also work in
  `defer:`, constructors, class `block:` clauses, field and parameter
  defaults, and arms of `sync`, `race`, `rush` and `branch`, including
  immediate first-success and `for` consumers. Waiting `for` bodies also
  work in concurrent arms and parameter defaults, including generic and
  interface-dispatched method defaults. Their source scope still determines
  which returns, breaks, effects and task operations are allowed. Waiting
  branches retain their source's mutable storage and cancellation cleanup.
  A wait hidden inside a refining helper counts toward `sync`'s two
  suspending arms; starting a background task does not.
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
  class adds. An unambiguous method captured as a value in `c2` retains
  that scope even when the class adds overloads. An interface without type
  parameters may also extend an instantiated interface
  (`intI := interface(container(int))`). A
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
  Omitted named arguments use the selected implementation's defaults,
  including computed defaults that read its receiver or earlier arguments
  and defaults whose types are opened or refined by dispatch. This also
  holds for spawned calls: defaults finish before the task starts, in the
  selected implementation's scope. Spawn arguments, including defaults,
  cannot wait. Supplied
  arguments run once in written order, then omitted defaults run in
  declaration order. Their effects count at the caller. Background tasks
  started in a suspending default belong to the caller; tasks started by
  the method's body belong to that method.
  The interfaces a class lists may not reach one interface at two instances
  (`class(pi(int), pi(string))`). Inherited field defaults see their
  own class's type parameters. A cast `square[S]` takes its type arguments
  from `S`'s, and one that would need more opens them, as a clause of a
  failure context only (see above). A method
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
  `var` locals need no heap permission, and immutable construction requires
  no operation-level allocation permission. A data type's declared construction
  budget still counts at every construction, even for an empty type. Lean proves that a
  function without `writes` keeps every existing object as it was
  (`Prog.accepted_no_writes`). A constant cannot hold an object with `var`
  fields or of a `<unique>` class, since it is computed at each use.
- **`block:`.** A class's `block:` clauses run when an instance is
  constructed, after its fields are given, those of the classes above it
  first, each class's in order; they see the fields by name, as a method
  does, and their effects are those of their code (a parametric class's
  too), checked within the class's construction budget. Field defaults and
  required mutable/unique allocation must fit the budget even when no caller
  constructs the type. Interfaces have no blocks.
- **`<unique>`.** A `<unique>` class (and every class below it) is
  comparable: `=` and `<>` test identity, so two instances with equal
  fields differ, and an alias equals its original.
- **Comparability.** Other classes and interfaces are not comparable (Book §4.9), nor
  is a struct or container that holds one.
- **Not yet supported** (each rejected with a message):
  - a cast that refines type arguments, opens them, or goes through a
    view (#243, #250, #351) outside any failure context, or inside an
    expression where the lifting of choices does not reach it (in a
    nested failure context of its own, such as an `option{…}` inside the
    clause, it is that context's);
  - in a `for`'s clauses, a clause past a generator after such a cast that
    uses its name in a branch of an `if` with a choice in its branches (#243);
  - after a cast that opens type arguments, a value of its failure
    context, or a name it binds that a branch or body uses, of a type that
    names them (#250): no type outside it can name them (it would be an
    existential type); and, where the cast takes the clauses after it, the
    refinement of a later cast whose object may name them and is not read
    by fields that are no `var`s from a cast's name (#250);
  - a branch of such a cast with a `return`, or a `break` that leaves it,
    where the `if`'s value is used at a type not known there (#243);
  - a variable, in generic code, of a class or interface type that
    requires an instance of itself (`Next:node(t)`) at type arguments that
    every class below it fixes otherwise: its hidden placeholder object
    (#157) would have to hold itself (no program can build an object of
    such a type: each would need another first, so use `?node(t)` for a
    link that may be absent);

## Mutation, macros, tooling

- **`set X? = v`** sets the value inside an option
  variable, and fails when the option is empty. It also works as a step of a
  path, as in `set S.Best? *= 7` and `set M[k]? = v`.
- **`let(defs){body}`** makes `defs` visible in `body`
  only. Its value is the body's. The definitions may also be braced, with
  the body after `do`: `let{X := 3} do X + 1`.
- **Clause macros** (`if{…}`, `for{…}`, `first{…}`, `first(…){…}` and
  `assert{…}`). Each takes clauses in braces, separated by
  `;`, `,` or new lines, run in a failure context; their value is the last
  clause's: a binding's name, or the expression's value. `if` and `for`
  may also take their clauses as `:` and an indented block or `.` and an
  expression, and are these macros unless `then` (`if`) or `do` (`for`)
  and a branch follow.
  - `if{c}` runs `c` and has no value; `if{c} else e` (also `else if{…}`) is
    the value of `c` when it succeeds, else `e`'s.
  - `for{c}` is the array of `c`'s values, for each way its generators,
    filters and bindings succeed: `for{X := 1..4; X * X}`.
  - `first{c}` fails when `c` does, else it is `c`'s value; `first(c){b}`
    runs `b`, which sees `c`'s names, once `c` succeeds, and fails when `c`
    does. Without a body after it, `first(…)` is a call, of a function no
    program can define (`first` is a [reserved name](#reserved-names)). `first` reads its
    clauses as `for` does, and takes `first(c). b`, `first(c) do b` and
    `first:` with the clauses indented, then `do:` and a body or nothing; a
    generator `X : Xs` in `first` parses and is refused as not supported
    yet.
  - `assert{c}` is a runtime error (as `Err()`, with no message) unless
    `c` succeeds.
  Without a [choice](#choice), `first` is the first and only success, and
  `first{c}` can only fail when `c` can. These macros
  take no body (`for{c} {b}` is refused), and `first` and `assert` before
  `{` are the macros (no struct can take either name). A void branch makes an
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

## Source profiles

Normal compilation supports the ordered multi-value constructs described
below. `--no-choice` selects an optional **choice-free source profile**:

```sh
openverse check Program.verse --no-choice
openverse core Program.verse --no-choice
openverse emit Program.verse --no-choice -o Program.vbc
openverse run Program.verse --no-choice --emit Program.vbc
openverse --no-choice run Program.verse hello do 'Run(Args)'
```

The profile rejects explicit `|` choices, both forms of `first` macro,
both forms of `for`, generator clauses, and ranges. This includes ordinary
array/map/string iteration through `for`, and a trivial `first{3}` or
single-element `for`. Array/map literals, indexing, ordinary `if`/`if{…}`,
`option{…}`, `logic{…}`, `not`, `and` and `or` remain available, with their
usual failure, binding and rollback behavior. A user-defined function named
`first` is an ordinary function when called without a macro body.

All loaded source is checked, including unused imported definitions,
file-backed `.value` expressions, methods, constructors, field and parameter
defaults, refinement conditions, and an optional command-line `do` expression.
A call or function value cannot hide an excluded construct in another
loaded definition. Rejection is a front-end error (exit 4) with its source
position, before execution or writing bytecode.

The profile leaves mutation, heap effects, output, explicit `loop`, recursion
and virtual-clock concurrency available under their ordinary checks. It is
a restriction on source choice/generator constructs. Compiler-generated
loops and internal first-success/dispatch helpers still implement admitted
source normally. Accepted source emits identical OVBC with and without the
profile; normal mode retains its existing choice behavior.

`--no-choice` can appear before the command, before its file, or among the
compiler options after the file. For `emit`, it can also follow `-o FILE`.
For `run`/`emit`, put compiler options before program arguments or `do EXPR`;
after the first program argument, subsequent tokens are arguments as before.
`--` ends option and `do` processing, passing everything after it literally
as `Args`. For example, `openverse run Program.verse --no-choice -- --no-choice`
passes the string `--no-choice` as one argument while enforcing the profile.

The compiler API uses `Front.Options.profile := .choiceFree` with `compile`,
`compileChecked`, `elabProgram` or `elabProgramCore`; `compileTops` and `compileWith` also accept
an optional profile. The default is `.full`.

Both profiles have deterministic execution: `Eval.det` / `Runs.det` establish
a unique Core outcome and output. Ordered source choices can yield several
values within that execution. Supporting choice in the compiler means it
can compile those constructs; the alternatives are evaluated at runtime.

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
    and the next one starts from the state the choice was reached in. One
    that reaches a `return` leaves the function, and one that reaches a
    `break` leaves the loop around the condition (#283): what it did stays,
    as with no choice, and the clauses after it and the other alternatives
    never run. The `break` runs the `defer:`s of the scopes it leaves, as
    any does, wherever the clauses after a choice are compiled to.
  - In a `for`, a choice is one more generator. An alternative whose own
    clauses (up to the next generator) fail is rolled back. One whose
    clauses succeed keeps their effects, even when the generators after it
    give no value, and each value runs the body, whose effects stay too.
    That is how every generator of a `for` behaves.

  ```verse
  var N:int = 0
  if (X := (set N = 1; 1) | (set N = 2; 2), X > 1) then Print("{X} {N}")   # 2 2
  loop:
      if (X := 1 | 2 | 3, set N = X * 10, X > 1, break) then Print("never")
  Print("{N}")                                                              # 20
  ```
- **Type.** The written type (`X:int = 1 | 2`), or the type of the
  variable or path that `set` writes, else the join of the alternatives'
  types, as for `if`'s branches.
- **`set L = a | b`** evaluates as `set` does: the indices of `L`'s path
  first, then for `op=` the old value, then the choice, so each alternative
  only runs the assignment. An alternative may have several values or
  clauses of its own, as a binding's may (#283): `set A[I] = (1 | 2) * 10 | 9`
  sets `A[I]` to 10, 20, then 9.
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
  member access, `?`, tuples, arrays, maps, string interpolation, the
  bounds of a range (`for (X := 1..(2 | 3))` is 1, 2, then 1, 2, 3: a
  range for each value of its bounds), the operands of `and` and the right
  of `or` (below), in the order they are evaluated:
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
  arguments (#243), including written types that use that refinement. An
  immediate body can start a task with `spawn`; its arguments run in the
  caller and must be immediate, while the spawned call can wait. Event
  notifications, subscriptions and subscription cancellation use ordinary
  immediate method calls. Their typed signatures determine whether a body
  waits. In a `for`,
  its body may wait or perform a non-rollback operation in a `<suspends>`
  function outside a failure context. Each current filter commits before
  the next generator's source or body runs; each body finishes before the
  producer advances. Mutable captures use their source storage, including
  read-only uses after a wait, so earlier background tasks and cancellation
  cleanup see the latest values. An immediate body may fail when the source
  context permits failure: this stops
  the whole `for` and retains that iteration's effects, just as in an
  ordinary `for`. An enclosing failure context can still undo them.
  A `return` in the body leaves the source function, stopping later
  alternatives. Its operand is saved before body cleanup; source cleanup
  then runs with the updated captured variables. This also applies to a
  shared consumer in a `<suspends>` caller, including waiting return
  operands and nested or lazy consumers. A return in a `for` clause
  also leaves the source function: a successful operand commits the
  current filter's writes before source cleanup; a failed operand still
  rejects that filter and rolls its writes back. Breaks inside the body's
  own `loop`s retain their targets. The body may itself consume a lazy choice
  with `for`, a first-success condition or an `option`, including generic and
  mutually recursive producers. These keep their own rollback boundaries;
  ordinary body cleanup also runs when that iteration finishes.
  Clause return operands still cannot wait inside their filter. Refining
  consumers retain the restrictions of their source scope, including in
  defaults, cleanup and concurrent arms. Failure of the selected branch's alternatives
  does not select the `else` branch.

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
  rolled back with them. A `return` or `break` inside the block that leaves
  it runs them too, as for any scope ([defer](#defer)): after the cleanup of
  the scopes inside the block it leaves, and after a `return`'s value:

  ```verse
  for (X := block{ defer: Print("d"); Y := 1 | 2; Y * 10 }) { Print(X) }   # d 10 d 20
  loop:
      if (X := block{ defer: Print("d"); Y := 1 | 2; if (Y = 2) then break; Y }, X > 5) then …   # d
  ```

  The operands of `and`, and the right of `or`, are lifted as blocks
  are (#283), each a scope of its own, as without a choice. `A and B` is
  `A`'s clauses, then `B`'s: for each value of `A`, in order, the values of
  `B` are the `and`'s. `A or B` is `if (T := A) then T else B`: the left of
  `or` takes its own first success, as it does with no choice on the right,
  and that value is then the `or`'s only one, the right never running; when
  the left has none, what it did is rolled back and the `or`'s values are
  `B`'s, taken by the context the `or` is in, as any choice's there. As for
  that `if`, the `or` adds no choice of its own: in a `for`, when its left
  succeeds, a value the filters after it reject undoes what came before it.

  ```verse
  for (X := (1 | 2) > 1 and (10 | 20)) { … }       # 10, 20
  for (X := M? or (5 | 6)) { … }                   # with M: its value; without: 5, 6
  if (X := M? or (6 | 8 | 9), X > 7) then …        # with M: its value, if > 7; without: 8
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

  Omitted field defaults run in declaration order too. A computed default
  before a choice runs once for that prefix; later values share any object
  it creates. Trailing defaults and the constructed class's blocks run for
  each completed value. Defaults retain their declaration scope and type
  arguments, including inherited defaults and implicit generic instances.
  A construction inside a recursive function computed eagerly keeps this
  order and these default types too. Its defaults and class blocks must
  meet that function's effect restrictions.

  Refused for now: a block with a range of its own as a branch; and
  a choice anywhere outside these failure contexts. (A field reached
  through a receiver that is not a variable or `Self`, as `F().Items[…]`,
  is read after the choice, since only the receiver's value is bound
  first.) `first{…}` with a choice can fail, so it must be in a
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
  `X := Upto[1, 3] | 9`, `set X = Upto[1, 3] | 9`): their values come in
  order, alternative by alternative (#283).

  When such alternatives' values are of different types
  (`A := Dup(a{}) | Dup(b{})`, `Dup` a generic function with several
  values), the clauses after the choice are compiled for each alternative
  (#335: once, through operation dictionaries, where they can be, else
  copied), and in them `A` has each alternative's own type: `A.M()` calls
  `a`'s `M` in one and `b`'s in the other, and an overloaded function takes
  each one's overload. So does what runs for each value: a `for`'s body, the
  value of `first{…}` or `option{…}`. What runs once, after the first
  success is taken (an `if`'s branches, the body of `first(…){…}`, the code
  after `first{…}`, `option{…}`, `if{…}`, `logic{…}`, `assert{…}`, `not`
  or the left of `or`), sees each name the clauses bind
  at one type, the join of its types in the alternatives (#283): their
  nearest common supertype, else `any` (classes with no common base, `int`
  and `string`), as for an `if`'s branches, and inside an array, an option
  or a tuple, element by element (`[]a` and `[]b` join as `[]any`, where an
  `if`'s branches of those types join as `any`). A name of one type in
  every alternative keeps it:

  ```verse
  a := class:
      M()<transacts>:int = 1 | 2
  b := class:
      M()<transacts>:int = 30 | 40
  Dup(V:t where t:type):t = V | V
  Main()<transacts>:void =
      if (A := (Dup(a{}) | Dup(b{})), X := A.M(), X > 2) then Print("{X}")   # 30: X an int, A an any
  ```

  Such an `any` can be passed to or kept where an `any` is taken, and
  nothing else ([any](#any)): using a name the condition binds as its
  class (`A.M()`, `A.F`, an argument of type `a`, a cast `a[A]`) is an error
  that names the choice; do that in the clauses after the choice, or take
  the values in a `for`. Classes with more than one nearest common
  supertype (two interfaces, neither below the other) have no join, and
  such a condition is refused, used after it or not, as such an `if`'s
  value is. A choice whose alternatives have no values or clauses of their
  own (`a{} | b{}`) has the join of its values' types, in the clauses after
  it too. So does one in the body of a function with several values (a
  `<decides>` one included), which is checked on its own with each choice
  at its alternatives' join (#283): `A.M()` after such a choice there is
  refused, though the copies at a call would compile.

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
  value is an ordinary call. So a function whose calls reach only
  overloads with one value has one value. The program is elaborated once
  to find the overload each call takes, then again with each call of an
  overload with several values inlined, wherever the call is (a function,
  a constant, a default, a class block, the entry expression). An overload
  may call its function's own name, so another overload, inlined there, or
  itself, recursive (below); and a recursive one may call an overloaded
  one, as it may call any function with several values. A call in
  the clauses after a choice whose alternatives' values are of different
  types, which are copied for each (#335), must take one overload in every
  copy.

  A method with several values works the same way (#283): a call
  `R.M(args)` evaluates `R` first, once, then is inlined like a function's,
  with `Self` the receiver, and so is `M(args)` in its class's methods and
  those of the classes below it. A recursive one is taken lazily, and a
  named parameter's default sees the fields. Each class or interface that
  declares `M` without `<override>` is the root of a family of its own:
  `M` and its overrides in the classes below it. `R.M(args)` is a call in
  the family of the root that `R`'s class is below (#283). When one class
  or interface declares `M`, overrides aside, that is known before types
  are checked. When unrelated ones do, the receiver's class tells:
  `M(args)` and `Self.M(args)` in a class's methods are in that class's
  family, and for any other receiver the program is elaborated once to
  find the receivers' classes, then again with each call in its family.
  So a class's `M` with one value stays an ordinary method wherever it is
  called, through a function too, and a function whose values come from
  another class's `M` through a receiver of that class has several values,
  as when one family has the name. The receiver may be of several of those
  classes where one call is compiled once for each alternative of a choice
  whose values are of different types (`for (A := (Dup(a{}) | Dup(b{})),
  X := A.M())`, #335): each alternative's call is in the family of its
  receiver's class, `a`'s or `b`'s, or of its `M` with one value. Where such
  a choice's first success is taken (an `if` condition, `first{…}`,
  `option{…}`, `not`, the left of `or`), the same, and what the condition
  binds has, after it, the join of its types in the alternatives, an `any`
  for unrelated classes (#283, see the alternatives with values of their own
  above). An overloaded `M` (#106) is a method
  for each of its parameter lists, each its own family: a call takes the
  list its arguments fit, as any call does, found as an overloaded
  function's call's overload is (the program elaborated once to find it,
  then again), and then its family as above; bare, through `Self` or
  `(super:)` too. So one list may have several values and another one.
  Lists are a class hierarchy's, so a call compiled for receivers of
  unrelated classes takes each one's list; one compiled for alternatives
  whose arguments' types pick two lists of one class is refused, as a
  call of an overloaded function with several values is there.
  A class below two roots of `M` (one
  listing two interfaces that both declare it) is refused when one of the
  families has several values. Such a
  method's name must be no field, no struct field, enumerator or member of
  a built-in type (`Length`, `Find`, `Signal`, …), no top-level name and no
  parameter or local. An
  interface's method is such a family's root too (#283): a call through
  the interface dispatches on the receiver's class, as for an overridden
  method; an interface's default implementation is the alternative for
  the classes that have none of their own. A generic class's or
  interface's method may be overridden too, including in a class that
  fixes, repeats, reorders or adds type arguments (`ibox := class(box(int))`).
  Dispatch tests the receiver's class and keeps its type equalities with the
  selected implementation. Added type arguments are read from that class,
  including for an inherited interface default. The declaring class's
  parameter and result types still describe the call. A generic class's
  method is a function generic over its class's type parameters, inferred
  from the receiver as at a generic call. Methods may also declare type
  parameters of their own, inferred from the supplied arguments, or from
  omitted defaults when the static receiver selects one implementation. Overrides
  may rename these parameters; their signatures and bounds are still checked.
  Defaults retain the implementation's type scope. Tuple-form super calls
  infer the ancestor's method parameters at that call, and covariant result
  selection substitutes both the receiver's and the method's arguments.
  A call dispatches on the
  receiver's class as any method call does, adding no choice of its own
  (#314): in a `for`, a value the filters after it reject undoes what came
  before it, the receiver's and the arguments' effects and the earlier
  clauses, unless the implementation reaches a choice of its own. `(super:)M(…)` calls the
  implementation above. Its tuple form `(super:)M((A, B))` uses the inherited
  parameter types as the current class sees them, including renamed or
  compound type arguments. The receiver and tuple are each evaluated once,
  in that order. A qualified call `R.(i:)M(…)` (#125) is a call in the
  family of the root `i` is below, dispatched as `R.M(…)` is. A method may
  call another method through `(super:)` too;
  extraction and helper functions retain the source class and receiver,
  so inherited implementations, overloads and defaults use that scope.
  A recursive overridden one is computed at the
  call (its implementations call each other through the dispatch), so
  it must be `<computes>`. Such a method is still checked as a member
  (`<final>`, its signature and effects against the one it overrides, an
  abstract one implemented). An override may return a subclass of its
  declaration's result, including in a generic family. The receiver's
  static class determines the result type: a `kennel.Get():dog` call
  permits dog fields, while the same object called through
  `shelter.Get():animal` exposes the animal result. A call has the effects of
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

  Cleanup stays with the scope that registered it. A returning branch runs
  only the `defer:` blocks it reached, from the innermost scope outward and
  last registered first, after saving each return value. A branch that falls
  through runs its cleanup before the rest of the function. A `defer:` after
  an earlier return path therefore runs only on paths that reach it; it may
  also be the final statement of a void function.

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

  A recursive one (that calls itself, directly or not, other than in a
  failure context of its code that takes the call's values, below) is not
  inlined. One shaped as a generator is taken lazily (#246): its clauses
  have no choice, and its last
  expression is a choice, or an `if … else …` whose branches are choices or
  values, each alternative a value with no choice in it or a whole call of
  the function itself. A branch that is an `if` with no choice and no call
  of the function in it is one value, not a branch to pick: its conditions
  are part of what that value does (#283). An alternative may also be a
  call of the function with code after it (#283): `Count(N - 1) + 1`,
  `Tell("x", F(N - 1))`, `Obj.F * 10 + F(N - 1)`. That code may set the
  function's `var`s: such a `var` is one object for the invocation, so the
  call's later values, and the later alternatives, see what a kept value
  set, and a rejected value's write is undone with it. What the
  alternative evaluates before the call (a field, a constant, a call of a
  function, a block's clauses), other than literals and the function's own
  names, runs once before the call, after the clauses, as the call's
  arguments do, and the code after the call uses its value. That code is the call's *return frame*: it runs on each
  of the call's values, as part of that value, and its result is the
  alternative's value. The last expression may also be a clause binding the
  choice, with such code after it, which then runs on each of the choice's
  values:

  ```verse
  Walk(N:int)<transacts><decides>:int =
      N > 0
      X := Walk[N - 1] | N         # the values of Walk[N - 1], then N
      Print("at {N} got {X}")      # runs on each, part of that value
      X + 1
  Count(N:int)<transacts>:int =
      if (N <= 0) then 0 else (Count(N - 1) + 1 | N)
  Main()<transacts>:void =
      for (V := Walk[2]) { Print("v {V}") }       # at 1 got 1, at 2 got 2, v 3, at 2 got 2, v 3
      if (V := Walk[2], V > 2) then Print("{V}")  # at 1 got 1, at 2 got 2, 3
      for (V := Count(2)) { Print("{V}") }        # 2, 2, 2
  ```

  Choice points may come in sequence (#283): the code after a call of the
  function, or after a choice, may reach another call or choice, and so on.
  A choice after a call (`X := T[N - 1] | N`, then `X | X + 100`), a call
  after a call (`U(N - 1) + U(N - 1)`, or `A := T(N - 1)` then
  `B := T(N - 1)`), a call after a choice (`X := 1 | 2`, then
  `V[N - 1] + X | N`), a choice in a call's argument (`G(N - 1 | N - 2)`),
  and a choice bound in a branch with code after it (`if (N <= 0) then 0
  else:` then `Y := Step(N - 1) + 1 | N * 10`, `set Local += Y`, `Local`) are
  all read as written: each point's values come in order, the code after it
  runs on each of them, the code before the next point once for each, and
  the values of the last are the function's, in spatial order. So the code
  between two points is what the first one's value does up to the second:
  in a `for` it stays once the second is reached, even if the filter then
  rejects every value after it, and where the first success is taken it is
  undone with the path that leads to no success, as for an inlined body:

  ```verse
  T(N:int)<transacts><decides>:int =
      N > 0
      X := T[N - 1] | N
      Print("t {N} {X}")      # once for each of X's values
      X | X + 100
  Main()<transacts>:void =
      for (V := T[2], V > 100) { Print("v {V}") }
          # t 1 1, t 2 1, v 101, t 2 101, v 101, v 201, t 2 2, v 102
      if (V := T[2], V > 100) then Print("first {V}")   # t 1 1, t 2 1, first 101
  ```

  A branch's code before its choice runs when the branch is selected, as a
  returning branch's does (below). The choice's values may be of another
  type than the function's (`S := "a" | "bb"`, then `T[N - 1] + S.Length`,
  or `S := "{T[N - 1]}" | "x"`). An alternative's code before a choice in
  it runs each time that alternative is taken, before that choice
  (`T(N - 1) | Tell("x", 1) + (1 | 2)`). A call of the function where the
  lifter takes a choice is a choice point there, in the same order: in a
  comparison's later operand (`5 > T[N - 1]`), a `set`'s value after its
  old value (`set K += T(N - 1)`, also as one alternative of a choice
  there, `set K += (T(N - 1) | 5)`, or of a `var`'s initial value), a named
  argument (`Tw(1, ?B := T(N - 1))`), a struct's or a class's field in its
  type's order (a class's superclass's fields first), `and`'s operands. An
  `if` in an expression with one in a branch is one too: its conditions
  run first, then the branch's values each go to the code after the `if`
  (`X := (if (N > 1) then T(N - 1) else (1 | 5))`), as do those of `or`'s
  right (`N = 0 or T[N - 1] > 1`) and of an `if` without `else` as a
  statement.

  A call of the function, or of another function with several values, in a
  failure context of its code (an `if`'s conditions, the operand of `not`,
  `option{…}`, `logic{…}` or `first{…}`, the left of `or`) or in a `for` of
  its code is no choice point of it: that context takes the call's first
  success, or the `for` all its values, as it would anywhere, while the
  function's own values are being taken, and the call's code takes its own
  in turn (#283). What a rejected attempt does is undone, and what the
  succeeding one does stays, as in any condition; a `for` keeps what each of
  its iterations does, as any `for` does. The context is a function of its
  own, called where it is, as a function that took the call's values would
  be: so a function whose only calls of itself are in such contexts is
  inlined, its recursion going through that function, as it does through
  any function that consumes it (`F(N:int):int = if (T(N) > 0) then 1 else 0`
  called by `T`):

  ```verse
  T(N:int)<transacts>:int =
      if (N <= 0) then 0 else:
          Print("t {N}")
          if (T(N - 1) > 0) then (N | 10 * N) else (N | 100 * N)
  Sum(N:int)<transacts>:int =
      if (N <= 0) then 1 else:
          var S:int = 0
          for (X := Sum(N - 1)) { set S += X }
          S | S + 1
  Main()<transacts>:void =
      for (V := T(2)) { Print("v {V}") }     # t 2, t 1, v 2, v 20
      for (V := Sum(2)) { Print("v {V}") }   # v 3, v 4
  ```

  A call of another function with several values in its code, outside such
  a context, is a choice point of it, as a call of the function itself is
  (#283): the callee's values each go to the code after the call, the callee
  taken with the function (its code one more of the function's, whatever its
  own shape: recursive or not, generic, a method, its values of another
  type), so its clauses are a failure context of their own, and when they
  fail it has no values and, in a `for`, what came before the call stays.
  A generic one is taken at one instance of its type parameters for a whole
  search, as a generic group's own functions are; a call of it at another
  is refused for now:

  ```verse
  Two(N:int)<transacts>:int = N | N + 5
  Digits(N:int)<transacts>:int =
      if (N <= 0) then 0 else Digits(N - 1) * 10 + Two(N)
  Main()<transacts>:void =
      for (V := Digits(2)) { Print("v {V}") }   # v 12, v 17, v 62, v 67
  ```

  A returning branch may contain plain clauses and
  nested conditionals before its value. A `return` at the end of the body or
  in an `if` branch ends that invocation, yielding its operand's values in order;
  statements after the return are skipped. These returns are normalized
  before choosing lazy or eager recursion. A selected branch's prefix runs
  before its values; if that prefix fails, the invocation fails without
  trying another branch. A strongly connected group of such functions is
  also taken lazily (#283), mutually recursive, each of that shape with its alternatives
  calls of the group's functions (or, as the last expression or a branch,
  one such call), all of one result type at the call:
  `Evens(N:int):int = N | Odds(N + 1)` with
  `Odds(N:int):int = Evens(N + 1)`. Its values are taken one at a time, as the place
  that takes them asks for them, in spatial order (depth first), so an
  infinite one works where the first success is taken, and a value never
  reached is never computed. A group may be generic: its members can rename,
  reorder or add type parameters, inferred from their arguments and the
  result expected by the consumer. Each member keeps the same parameter
  types throughout one search, as a self-recursive lazy generator does.
  A pure mutual group that changes those types on recursive edges keeps
  the eager route described below, including its restrictions and errors.
  A returning `any`-valued group with recursive edges in an incomplete tail
  conditional also uses that eager route, so the conditional erases all
  yielded values to `void` while explicit returns retain their operands.

  When parameters are named, each recursive call
  evaluates positional arguments first, then named arguments as written, then
  omitted defaults in declaration order, as an ordinary call does. Defaults see the
  declaration's scope and earlier parameters. A recursive self or mutual call
  can supply its positional parameters as one tuple, including when named
  parameters follow or take defaults. The tuple uses the producer's current
  parameter types, and is evaluated once; a method evaluates its receiver first.
  A tuple-valued single parameter remains one parameter. A call evaluates its arguments
  first; when its clauses fail, it has no values, and what its arguments did
  stays, as for a recursive call computed at the call. It may have effects:
  - in a `for`, its clauses run as its values are taken, between the
    iterations, and stay, as a `for` keeps the effects of clauses before a
    choice; what a value does is undone with its iteration when the
    filter rejects it, the return frames it went through included (#283);
  - where the first success is taken (an `if` condition, `first{…}`,
    `option{…}`, `logic{…}`, `not`, the left of `or`), effects are undone as
    the Verse Calculus undoes them: what a value does with that value, and
    what a call's clauses, the conditions of its last `if` and its
    arguments do with all the values that call leads to, when the context
    rejects them all (a tree walk that prints keeps only the path to the
    value taken). When those have effects, the call and the clauses after
    it run as a function of their own, recursive. This includes generic
    functions and methods, with generic values, written types and `Self`.
    Calls of `(super:)` retain the enclosing source method's inherited
    implementation, qualified slot and overload lookup. Named arguments
    and omitted defaults keep their ordinary evaluation order.

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
  then takes them from (#235). So do those with return frames that are so
  effect-free (#283): taken either way, their values are the same, but an
  infinite one does not stop. Those with return frames that have effects
  are taken lazily.
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

  A return in first-success clauses leaves the source function, and a
  break the loop around them (#283), including after an effectful lazy
  generator. Its operand is saved before cleanup;
  updated mutable captures reach source cleanup before it runs. A failed
  return operand rejects that search path and tries the next alternative.
  Shared helpers retain generic result types and witnesses even when only
  the return type mentions a parameter.

  Refused for now: a recursive one that is not of the generator shape
  above (return frames and choice points in sequence included) and is not
  `<computes>`, keeps local state, or may print or call `Err()`. Its choice
  points must be where a choice is lifted from (a comparison's later
  operand, a `set`'s value, a named argument, a struct's field, `and`'s
  operands, an `if`'s branch, the right of `or`) (#283). Also a recursive one with a `defer:` of its own, or called by a recursive one (its body a function's, where it would run once), one with a `return`
  other than at the end of its body or in an `if`'s branches, a method of a class or
  interface below two others that each declare its name without `<override>`,
  `<suspends>`, one used as a function value, and, since its body is inlined where other names may be
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
`array{15.61, "Message", 3}` (a `[]any`), and so does a name bound by the
first success of the clauses after a choice whose values are of such
types, after them ([Choice](#choice), #283). Classes with two common
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
Whatever the condition: an index, a `<decides>` call or a cast among its
clauses, first, later or alone, takes it as any (`if (X := Xs[1], X > 1)
then array{X} else array{}` is a `[]int`), and a cast that refines type
arguments types the branch under its refinement (#243, #583).

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
- `Sinh`, `Cosh`, `Tanh`, `ArSinh`, `ArCosh`, `ArTanh` and
  `Lerp(From, To, Parameter)` never fail (#490). These seven require
  `<reads>`, as their upstream declarations do. For example,
  `Blend(A:float,B:float,T:float)<reads>:float=Lerp(A,B,T)`.
  Their domains and special values are listed below.
- A program may define functions named `Round`, `Int` or any of these
  (and constants named `PiFloat`, `Inf`, `NaN`): its definition then
  replaces the built-in for every call, whatever the argument types. A local
  or a method may not take those names; a field may, and in its class's
  methods the name still means the built-in.
- `ToString` gives the shortest decimal that reads back as the float, laid
  out as Python's `repr` (`98.5`, `1.0`, `1e+16`, `1.5e-07`), and `Inf`,
  `-Inf`, `NaN`.

### Scalar Math API inventory (#490)

The inventory is pinned to the Book's
[Runtime API at `beaa719`](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/api/verse_runtime_api.html#math).
Its seven previously missing float declarations are public, native,
non-failable and marked `<reads><predicts>`; none has a release-version,
experimental or deprecated annotation there. Epic also publishes
[Sinh](https://dev.epicgames.com/documentation/fortnite/verse-api/versedotorg/verse/sinh?lang=en-US)
and [Lerp](https://dev.epicgames.com/documentation/fortnite/verse-api/versedotorg/verse/lerp?lang=en-US)
in its released API documentation. This does not date their first release
or establish a bit-for-bit engine conformance claim.

| Function (all inputs/results `float`) | Domain and special values |
|---|---|
| `Sinh(X)` | Odd; infinities preserve sign; overflow gives infinity. |
| `Cosh(X)` | Even; zero gives 1; either infinity and overflow give positive infinity. |
| `Tanh(X)` | Infinities give -1/+1; large finite magnitudes round to those limits. |
| `ArSinh(X)` | All real inputs; infinities preserve sign. |
| `ArCosh(X)` | Inputs below 1 give NaN; 1 gives zero; positive infinity stays infinite. |
| `ArTanh(X)` | Magnitudes above 1 give NaN; -1/+1 give negative/positive infinity. |
| `Lerp(From,To,Parameter)` | Weighted sum; parameters outside [0,1] extrapolate. |

All seven propagate NaN and use OpenVerse's canonical zero. Hyperbolic
functions use libm directly, preserving tiny arguments and avoiding
intermediate overflow in the inverse functions. `Lerp` evaluates its three
arguments once, left to right, then computes
`From*(1-Parameter)+To*Parameter` with each operation rounded separately.
Finite endpoints return the corresponding input exactly. It does not
short-circuit non-finite endpoints: `Lerp(1.0,Inf,0.0)` is NaN because
`Inf*0.0` is NaN. Even finite extrapolation can overflow its products.

The other pinned float Math declarations and float-util conversions were
already supported. The pinned Math page declares only an integer `Clamp`,
the median of its three arguments, so the order of `A` and `B` does not
matter; Epic's published API adds
[`Clamp(Val:float, A:float, B:float)`](https://dev.epicgames.com/documentation/en-us/fortnite/verse-api/versedotorg/verse/clamp),
whose comparisons order NaN above +Inf, and
[`Sgn`](https://dev.epicgames.com/documentation/en-us/fortnite/verse-api/versedotorg/verse/sgn)
of an int and of a float (NaN of NaN), which the Book's tests call
(`Math.versetest`); openverse has the three, written with Verse Core's
comparisons, each argument evaluated once, in order. Epic's API also
declares `IsFinite` as a method, `(X:float).IsFinite()<decides>:float`:
`F.IsFinite[]` is `IsFinite[F]`. Vector/rotation APIs
are outside this scalar inventory. Existing mathematical built-ins retain
their earlier effect handling; this change enforces `<reads>` on the new
seven without changing those existing programs. The broader effect audit
is tracked in #494; `<predicts>` is not currently enforced.

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
- There are no rational literals and no `ToString` of one.
- Arithmetic is an **OpenVerse extension** (#489): `+`, binary `-`, `*`
  and unary `-` on rationals return a rational with `<computes>` behavior.
  Either binary operand may be an int. `/` on rational/rational or mixed
  int/rational operands is `<computes><decides>` and fails on a zero
  divisor. `+=`, `-=`, `*=` and the failable `/=` work on rational mutable
  values and paths, with the usual read-before-right-operand order and
  rollback rules. Int/int and float arithmetic keep their existing behavior.

The [Book's pinned rational section](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/02_primitives.md#rationals)
documents quotient construction, conversions and normalization. Its
[operator table](https://github.com/verselang/book/blob/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs/04_operators.md#basic-arithmetic)
does not specify the arithmetic family above. These overloads are an
OpenVerse design decision, not a claim of released-UEFN conformance.

In Verse Core a rational is the tuple of its numerator and denominator, in
lowest terms with a positive denominator. Its parts are 64-bit ints, so
`X / Y` raises the overflow error when the result's numerator or
denominator is out of range, as in `(-2^63) / -3` or `1 / (-2^63)`.
Arithmetic checks these bounds **after reduction**, using exact intermediate
products/sums. Cancellation can therefore succeed even when intermediate
values exceed int64; a reduced result outside the range raises overflow,
which is an error rather than a recoverable failure. Zero is always `0/1`.
`Floor(R / S)` and `Ceil(R / S)` first compute the rational quotient; the
existing direct int/int rounding path remains unchanged.

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
non-ASCII character in quotes is a `char32` literal (`'😀'` is `0u1F600`,
Book of Verse ch. 1, "Character Literals"); an ASCII one is a `char`.

The conversions between chars, code points and ints are methods, as the
Book's Runtime API ("char and char32") declares them; each is written
with Verse Core's existing operations:

| Method | Result | Fails |
|---|---|---|
| `C.ToCodeUnit()` of a char | its code unit, 0 to 255 (a binary search over the table of the 256 chars) | never |
| `C.ToAsciiChar32[]` of a char | the char32 of the same number | above 127: a byte 128 to 255 is part of a multi-byte sequence |
| `C.ToCodePoint()` of a char32 | its code point (the same int in Verse Core) | never |
| `C.ToAsciiString()` of a char32 | its UTF-8 encoding, one to four chars, as `ToString` gives | never |
| `N.ToChar[]` of an int | the char of that code unit | outside 0 to 255 |
| `N.ToChar32[]` of an int | the char32 of that code point | below 0, from 0xD800 to 0xDFFF (surrogates), above 0x10FFFF |

Those that cannot fail are called with `()`, the others with `[]`.

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

The [scheduler conformance audit](research/scheduler-conformance.md) pins the
source comparisons and trace evidence for the reference clock, event wake
order, cleanup, event transactions and standalone host lifetime (#495).

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
  subclasses override `Run`). Its receiver and supplied arguments run once
  in caller order, then omitted defaults run in declaration order, before
  starting the task. This includes defaults using receiver fields, refined
  arguments and opened types. Arguments and defaults cannot wait. The
  task runs at once up to its first wait. The value is a `task(t)`, where
  `t` is the result type at the receiver's static declaration, including
  when an override returns a narrower class. `T.Await()` waits for the task to end and
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
- **Library types.** `event`, `sticky_event`, `task`, `subscribable_event`
  and `cancelable` are available wherever their types are used, including
  immediate functions, casts, unused loaded definitions, nested annotations,
  imports and command-line `do` expressions (#518). Type use alone does
  not require `<suspends>`; waiting and cancellation still follow their
  ordinary effect/context checks. A program's own definitions and module
  names retain their meaning, including methods named `Signal`, `Await`
  or `Cancel`. Library dependencies retain their built-in meaning when a
  program owns one of those type names. Undemanded helper types do not
  reserve names against unrelated generic parameters or callbacks.
- **`event`.** An `event(t){}` has `E.Await()`, which waits for the next
  `E.Signal(X)` and gives `X`, and `E.Signal(X)`, which wakes every task
  waiting at that moment, each with `X` (the API's reading; the Book's text
  says both "each awaiter" and "exactly one"). The woken tasks go on in the
  scheduler's order (`Main`, then tasks in the order they were started,
  arms in source order), not in the order they began waiting. With
  `--event-fifo` (`openverse run` and `emit`, opt-in until a default is
  chosen, #513) they go on in the order they began waiting, the published
  API's: once the task that signalled waits or ends (`Signal` returns
  first), each woken task's turn comes in that order, before the
  scheduler's own order goes on; tasks they wake take their turns after
  them. A task is a spawned task, `Main` or a `branch`, and waiters in the
  arms of one task's `sync`, `race` or `rush` each take their own turn too
  (resuming the task for one arm's turn leaves its other woken arms
  waiting for theirs), also a `rush` arm that goes on after the `rush`
  (a task of its own then), signalled before its first turn as one. A
  waiter cancelled before its turn does not go on, and a wait
  cancelled before the `Signal` (a `race` it lost) is no waiter; once
  `Main` ends, so does the program, also in the middle of the turns. A `Signal` with no one waiting is lost, and `Signal`
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
  With `--signal-no-rollback` (`openverse run`, `emit`, `check` and `core`,
  opt-in until a default is chosen, #515), a program that may call an
  event's `Signal` from a failure context is refused before it runs or is
  emitted. A failure context is an `if`'s condition, a `for`'s clause, a
  `<decides>` function's body, `option{…}`, `logic{…}`, `not`, the left of
  `or`, a `first{…}` or a `do` expression, with everything that runs
  inside it: a `block`, a named argument's default, a `defer:` (but not
  one that a `return` or a `break` out of the failure context runs:
  leaving it that way commits it). What it
  runs counts: the functions it calls, the `block:`s of the classes it
  constructs, the initialisers of the constants it uses, every
  implementation a method call may pick, and every function of a function
  value's type that is given as a value (conservatively), any of which may
  reach the `Signal` of any kind of event. The error names the way to the
  `Signal`. An `if`'s branches and a `for`'s body are not failure contexts
  (unless the `if` or `for` is in one), also when the compiler moves the
  body into a function of its own, and neither is the call a `spawn`
  starts (its task runs it later; its arguments count). `Subscribe` and
  `Cancel` in a failure context stay admitted, undone as above.
  A `subscribable_event()` is one without a value: `E.Signal()`,
  `E.Await()`, and functions of type `type{_():void}` to subscribe (#220).
  It is an `event(void)`, but not a `subscribable_event(t)`, whose
  functions take a value.
  The `subscribable_event()` shorthand selects the built-in no-payload
  form; a source-defined class of that name uses its ordinary construction
  syntax with explicit type arguments when parametric. A program using
  the built-in subscribable form cannot also define its own `cancelable`.
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
  uses the binary64 product `T = 30·S` and ties-to-even `Round(T)`, at least
  one tick, for a supported nonnegative finite input. It always yields,
  including either signed zero or a positive subnormal. The product must
  be below `2^63`; the largest supported binary64 duration is exactly
  `307445734561825792.0` seconds, giving `2^63 − 2048` ticks. The next
  binary64 duration, `307445734561825856.0`, is outside this domain.
  An unsupported finite input terminates immediately with `error: user`;
  it is a fatal runtime error, not a failable result or an infinite wait.
  `Sleep(Inf)` alone is the intentional indefinite timer; a negative or
  NaN input returns at once. The virtual clock starts at zero and ranges
  through `2^63 − 1`: if current time plus the requested ticks exceeds
  that maximum, checked addition terminates with `error: overflow`, without
  wrapping or clamping. These are reference-clock limits, not measured
  engine limits (#514); ordinary source overrides do not alter the
  scheduler's primitive rounding or infinity classification.
- **The program.** A suspends `Main` runs under the scheduler. The program
  ends when `Main` does, even if tasks are still running; unfinished
  unstructured tasks are not cancelled, so their pending defers do not run.
  If `Main` waits
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
| `return` or `break` inside a failure context | unspecified | leaves the function, or the loop around the context; no rollback of what the condition did, also after a choice in it, whose alternatives that failed before were rolled back (#283) |
| Scope of the operands of `A and B` | "Variable bindings do not escape from logical operations" (§3.4) | each operand is its own scope: names defined in `A` are not visible in `B`, and names from neither side escape the `and` |
| Comparability | `comparable` covers the primitive types, enums, structs and containers of comparable types (§4.9) | so is every openverse type, except a type parameter not declared `subtype(comparable)` and the containers of one |
| Inferring type arguments | not described | first-order matching against the expected result type, then the arguments; no subtyping other than `false` (matches anything) and `void` (accepts anything) |
| Access specifiers other than `<public>` | `<internal>` (the default), `<private>`, `<protected>`, … (ch. 16) | a module member is `<public>` or internal (visible in its module and its submodules); other specifiers, and a struct field's, are accepted and not enforced |
| `ToString` of a float | "the shortest" (an example: `98.5`) | the shortest decimal that reads back as the float, the closest of the shortest, in Python's `repr` layout (exponent at `≥ 1e16` and `< 1e-4`); `Inf`, `-Inf`, `NaN` |
| `NaN < X` | not stated | fails (IEEE: NaN orders with nothing); `NaN = NaN` succeeds (the Book) |
| `=` between different types | not stated | refused when two scalar types (int, float, char, …) meet at the same place, also inside containers (`array{1} = array{1.0}`), as Verse Core holds them differently |
| Ordering of rationals | not stated (§2 lists `<` … for `int` and `float`) | exact (by continued fractions, so it cannot overflow), and an int compares with a rational |
| Order of a choice's values | (not in the Book; the Verse Calculus: spatial) | spatial: the leftmost choice varies slowest, as nested generators do (#208) |
| Code before a choice | (the Verse Calculus is pure) | runs once, also within an expression (the operands before the choice are evaluated first, as written); each alternative runs the code after the choice, from where the choice was reached; in an `if` or `first{}`, one that leads to no success, and to no `return` or `break`, is rolled back (as backtracking does); in a `for`, the choice is a generator, so only an alternative whose own clauses fail is (#208) |
| A choice in an operand of `and` or `or` | not stated (the left of `or` is a failure context, the right is not, §6.2) | `A and B`: `A`'s clauses, then `B`'s, in the context the `and` is in, so `B`'s values for each of `A`'s; `A or B`: `if (T := A) then T else B`, so the left's first success, if it has one, is the only value (the right is not tried when what follows fails), else the right's values, taken by the context the `or` is in (all of them in a `for`), not only its first (#283) |
| A call of another function with several values in a recursive one's code | not stated (the Verse Calculus: a call is its body) | a choice point of the recursive one, taken with it: when the callee's clauses fail it has no values, and, in a `for`, what came before the call stays, as at a call of the recursive one itself (a lazily taken call is a generator of its own), not undone as at an inlined call (#283) |
| A recursive function with several values whose only calls of itself are in failure contexts of its own code | not stated (the Verse Calculus: a call is its body) | inlined, as a function recursive only through another function that consumes it is (the contexts are functions of their own): where its clauses fail in a `for`'s clauses, what those clauses did since their last generator is undone with them, as for any inlined call, not kept as at a lazily taken call, which is a generator of its own (#283) |
| Precedence of `\|` | (not in the Book) | below `+`, above the comparisons: `X = 1 \| 2` is `X = (1 \| 2)` (#208) |
| `Sleep(0.0)` | "may resume in the same tick" (ch. 14); the API reference: it always yields | always yields: resumes in the next tick (#156) |
| `Sleep(S)` rounding | no fixed 30 Hz rounding rule in the pinned chapter or cited Epic timing description | binary64 `Round(30·S)`, ties to even, at least one tick: `Sleep(0.1)` stays at 3 ticks despite binary floats (#156); bounded inputs and checked clock accumulation follow the explicit reference policy above (#514) |
| End of a program with tasks | not stated | the program ends when `Main` does; a `Main` that waits with no task able to run is an error (exit 2) (#156) |
| Order of a `subscribable_event`'s functions | not stated (ch. 14's example lists them in subscription order) | subscription order; the tasks awaiting the event are woken first and go on after `Signal` returns (#210) |
| Event waiter resumption | Epic's event/Signal API specifies suspension order | Main/spawn/source-arm scheduler order by default; with `--event-fifo`, suspension order across tasks and arms, after `Signal` returns and the signalling task waits; the default is undecided (#513) |
| Signal in a failure context | the published Signal API describes no_rollback, alongside rendered transacts bits; versioned compiler behavior needs separate evidence | transactional Signal and callbacks are allowed and rolled back by default; with `--signal-no-rollback`, a program that may signal an event from a failure context is refused before it runs; the default is undecided (#515) |
| Extent of a `<#>` comment | "everything indented by four spaces on subsequent lines" (§1.1) | the rest of the `<#>` line and every following line indented more than that line, whatever the amount (blank lines included); `<#>` may also follow code on a line |

## Not supported in v1

`ToString` of rationals (see [rational](#rational)), float functions beyond those of [float](#float),
the class features listed under [Classes](#classes), struct methods (Verse structs have none; classes do),
`weak_map`, module paths `using{/Verse.org/…}` (accepted and ignored) and paths as values, the
specific overload/call gaps listed under [Overloading](#overloading), nested
functions and lambdas (see [release evidence and proposed design](research/closure-design.md)), choice beyond [Choice](#choice), concurrency beyond [Concurrency](#concurrency), and the unsupported
effect/construction contracts listed under [Effect contracts](#effect-contracts).
