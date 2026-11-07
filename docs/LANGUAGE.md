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
| Mutation | `set X = e`, `set X += e` (`-=`, `*=`), `set A[i] = e` (fails out of range; returns `e`) | §3.3 |
| Blocks | indented (`:`), braced (`{ }`), inline (`then`/`do`), `block:`, `( a; b )` sequences | §2.2–2.4 |
| Operators | `* + -`, unary `-`, comparisons `= <> < <= > >=` (failable, return the left operand, chains check every pair), `and`, `or`, `not`, `?`, `.Length`, `A[i]`, `T(k)` | ch. 4 |
| Failure | failure contexts (`if` conditions, `for` clauses, `option{}`, `logic{}`, `not`, left of `or`, `<decides>` bodies) with rollback of `var` writes **and output** | ch. 8 |
| Control | `if`/`else if`/`else` (all styles, `if:`…`then:`), `for` with `X : array`, `I -> X : array`, `X := a..b`, filters, bindings, several generators (cartesian product), `loop`/`break`, `return`, `case` with literal patterns and `_` | ch. 7 |
| Functions | recursion, mutual recursion, `<decides>` (called with `F[…]`), named parameters `?P:t = default` passed as `?P := e` (positional, then named as written, then defaults), other effect specifiers accepted and ignored | ch. 6, 13 |
| Parametric functions | `F(X:t, … where t:type, u:subtype(comparable))`: type parameters in parameter types, the result type and local declarations; type arguments inferred at each call (see [Parametric functions](#parametric-functions)) | Types: where clauses |
| Structs | `name := struct:` with typed fields and defaults, `name{F := e, …}`, `S.F`, `set S.F = e` / `op=`, structural equality (a struct is the tuple of its fields in Verse Core) | ch. 9 |
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
- **Monomorphised.** Each distinct list of type arguments becomes its own
  Verse Core function, named like `Find(string)`. Verse Core, the OVBC format
  and the C runtime know nothing of generics, and every instance is checked by
  `Prog.checkTypes` like any other function (see [`DESIGN.md`](DESIGN.md)).
- **Limits.** A function that calls itself at ever larger types
  (polymorphic recursion) is rejected, as are named parameters, a generic
  `Main`, and several constraints on one type parameter (also unsupported in
  the Book).

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
`char32`, classes, interfaces, open enums, struct methods, `ConcatenateMaps`,
`weak_map`, nested `set` paths (`set A[i].F`), modules beyond
ignoring `using`, overloading, defaults that refer to earlier parameters, nested
functions, `first`, `defer`, refinement types, concurrency (`spawn`, `sync`,
`race`, `rush`, `branch`, `<suspends>`), `weak_map`, and effect checking for
`<reads>`/`<writes>`/`<computes>`. Comparing arrays with tuples (`array{1,2}
= (1,2)` succeeds in the book) is not supported: arrays and tuples are
different values and compare unequal.
