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

- The language: [Supported](#supported) · [Source text](#source-text) · [Parametric functions](#parametric-functions) · [Effect contracts](#effect-contracts) · [Function values](#function-values) · [Extension methods](#extension-methods) · [defer](#defer) · [Overloading](#overloading) · [Parametric structs](#parametric-structs) · [Classes](#classes) · [Attributes](#attributes) · [Mutation, macros, tooling](#mutation-macros-tooling) · [Warnings](#warnings) · [Source profiles](#source-profiles) · [Choice](#choice)
- More types: [any](#any) · [comparable](#comparable) · [Weak maps](#weak-maps) · [Module-scoped variables](#module-scoped-variables) · [Types as values](#types-as-values) · [Equality and the empty value](#equality-and-the-empty-value) · [Refinement types](#refinement-types) · [Type aliases](#type-aliases) · [float](#float) · [Bitwise functions](#bitwise-functions) · [rational](#rational) · [char32](#char32)
- Programs: [Modules](#modules) · [Access](#access) · [Shadowing](#shadowing) · [Qualified names](#qualified-names) · [Programs of several files](#programs-of-several-files) · [Concurrency](#concurrency)
- [Readings openverse takes](#readings-openverse-takes) · [Not supported in v1](#not-supported-in-v1)

## Supported

| Area | Supported | Book |
|---|---|---|
| Comments | `#` to the end of the line, nested `<# … #>`, `<#>` indented comments (the rest of the line and every following line indented more than it; see [Source text](#source-text)) | ch. 0 |
| Literals | `int` (decimal, `0x` hex; must fit in 64 bits), `'c'` `char` (`c` an ASCII character other than a line break, a tab included, or an escape; a non-ASCII one, `'é'`, is a `char32`, Book of Verse ch. 1), `0oHH` `char` code unit (one or two hex digits, not octal: `0o41` is `'A'`, `0o9` is a tab), strings with escapes and `{expr}` interpolation, `true`, `false`, `0uHHHHHH` `char32` (a Unicode scalar value, up to `0u10FFFF`, no surrogates), `float` `1.5`, `2.0e-7`, `1e3`, `12.34f64`, `1234f64` (digits, then a point and digits or an exponent or both, or the suffix `f64`, which may follow either; the nearest double, which must be finite: `2.0e308` is refused; `f32` and `f16` are read and refused as not supported); paths `/Verse.org/Random` parse (in `using{…}`, ignored when in a package openverse knows, `/Verse.org/…`, `/Fortnite.com/…`, `/UnrealEngine.com/…`, and refused otherwise, as naming nothing, ch. 16, `Using2.versetest:94`; as values, refused; see [Source text](#source-text)) | §1.3–1.7 |
| Types | `int`, `logic`, `char`, `char32`, `any` (see [any](#any)), `comparable` (see [comparable](#comparable)), `rational` (see [rational](#rational)), `float` (see [float](#float)), refinement types `type{_X:int where 0 <= _X, _X <= 120}` (see [Refinement types](#refinement-types)), `string` (= `[]char`), `[]t`, `?t`, `tuple(…)`, `void` (which takes any value; `tuple()` is the type of the empty value alone, see [Equality and the empty value](#equality-and-the-empty-value)), `message` (a localized message, `X<localizes>:message = "…"`, `F<localizes>(N:int):message = "… {N}"`, rendered by `Localize` and joined by `Join`; openverse has no culture, so a message is its default text, an int written with comma separators: ch. 12, [the rule](research/book-forms-rules.md#localized-messages)), `false` (the type with no value, below every type: a function whose result is `false` never returns, ch. 2, [the rule](research/book-forms-rules.md#false-as-a-type); `true`, the type of the empty value alone, as `tuple()` is, below `logic`, [the rule](research/book-forms-rules.md#true-as-a-type)), function types `type{_(:int)<decides>:int}`, with named parameters `type{_(:int, ?B:int):int}`, and `int->int` (see [Function values](#function-values)); type aliases `player_id := int`, `pair(t:type) := tuple(t, t)` (see [Type aliases](#type-aliases)); types as values of classes and interfaces, `subtype(c)`, `castable_subtype(c)`, `concrete_subtype(c)` and `type` (see [Types as values](#types-as-values)); a conversion written as a call, `int(0)`, `void(0)`, `(?int)(option{0})`, `s(s{})`, of a value of a type that is a subtype of the one named; a tuple converts to an array of its elements where an array is expected, and compares with an array as one (`array{1,2} = (1,2)`) | ch. 2–3 |
| Definitions | top-level functions `F(X:t, …)<effects>:t = body`, top-level constants `C:t = e`, which state their type there as in a module (ch. 16: "type inference with `:=` alone is not allowed"; `C := e` names a type, when `e` is one: [Type aliases](#type-aliases)) (definitions on one line, at the top level, in a module or in a block, are separated by `;` or `,`: `X:int=0, Y:int=0`; a constant may use one defined before it in its own scope, a module's or the top level's, and one of another module or of an enclosing scope wherever it is defined, as the Book's tests have it (`DefaultValueAssignment.versetest` 102, 128); not itself, directly or through other constants; and its value has no side effect, writing nothing, also through what it calls or constructs, as the Book's tests have it, `DefaultValueAssignment.versetest:199`, `ModuleDefinitions.versetest:278`, `ParametricTypes.versetest:465`: a function with no heap specifier, or a class or struct with none, has `<transacts>`, and so writes, [the rule](research/book-remaining-rules.md#a-module-constant-has-no-side-effect)); module-scoped `var X:weak_map(k, v) = map{}` (see [Module-scoped variables](#module-scoped-variables)); locals `X := e`, `X:t = e`, `var X:t = e`, and a tuple destructured, `(X:int, _, Z:string) = e` (each named element a local of the block, `_` skipping one, `e` evaluated once); no shadowing; no name defined twice in a scope but [overloaded](#overloading) functions; no [reserved name](#reserved-names) | §3.1–3.4 |
| Mutation | `set X = e`, `set X += e` (`-=`, `*=`), `set A[i] = e` (fails out of range; returns `e`), and paths `set S.F.G = e`, `set A[i][j] op= e`, `set M[k].F = e`: indices and keys evaluated once, left to right, then the new value, then the variable rebuilt (for `op=`, the old value is read after the new one, from the variable as the new one left it, which is then rebuilt from that: `set X += e` is `V := e; set X = X + V`, the Book's tests, `ArrayAppend.versetest` 140, 183); an index out of range or a missing intermediate key fails, while the last key of a path inserts | §3.3, §3.5, §9.3 |
| Blocks | indented (`:`), braced (`{ }`), inline (`then`/`do`), `.` and an expression on its line wherever `:` or `{…}` may start a body (`if (c). e else. f`, `for (X:Xs). e`, `spawn. F()`, `loop. break`; also `option`, `logic`, and `array` and `map`, whose `:` blocks separate their items by `,`, `;` or new lines: `array:` and the lines `1`, `2`; in braces an array's elements are separated by commas, or by `;` and new lines, not both: `array{1; 2; 3}`), `block:`, `( a; b )` sequences, also as an argument (`F(Log(); 42)` passes 42) and as a `case`'s value (`case(a; b)`); `;` and new lines separate the items of a block, and `;` may end a line or a braced block (`{1; 2;}` is `{1; 2}`) (the next item then follows the line rules, so a class's last field may end in `;`); in a block, statements that commas join on a line are a tuple (ch. 1, "Semicolons vs Commas", and its tests, `SemicolonsVsCommas.versetest` 70, 95, 100: `{1.0, 2}` is a `tuple(float, int)`, `option{1, 2}` holds `(1, 2)`, `for (X := 1..2) {3, X}` is an array of pairs), definitions joined so are the block's definitions in turn (`X:int = 0, Y:int = 0`), and a group of definitions and values is each in order, a definition visible to what follows it, then the tuple of their values (`option{V := 3, V > 0, V}` holds `(3, 3, 3)`, a `var`'s value taken where it is defined); the clauses of `if`, `for`, `first` and the clause macros, the arms of `sync`, `race` and `rush`, a construction's fields and an array's or map's items keep commas as separators; a comma that starts a line is not the block's but the list's around it; a body after `:` may be empty wherever one may be written, as `{}` may (`class:`, `struct:`, `then:`, … whose next line is no deeper than the construct, or nothing follows); a function's or method's braced body may put its `{` on the next line, at the definition's column; a value after `=`, `:=`, `set … =` or a `case` arm's `=>` that starts a later line, deeper, is the indented block of those lines (`Value :=` and the lines `1`, `2`, `3` is `3`; and the line `1, 2, 3`, `(1, 2, 3)`), as a function's body is | §2.2–2.4 |
| Operators | `* + -`, unary `-`, comparisons `= <> < <= > >=` (failable, return the left operand, chains check every pair, but `<>` is left-associative: `1 <> 2 <> 1` is `(1 <> 2) <> 1`, which fails, as the Book's tests have it, `Associativity.versetest:6-9`, [the rule](research/book-forms-rules.md#-is-left-associative); `=` and `<>` of any two comparable types, by value: see [Equality and the empty value](#equality-and-the-empty-value)), `and` (a scope of its own, ch. 7: names its left operand defines are visible on its right, and neither side's escape; `A and B and C` is `(A and B) and C`), `or`, `not` (below the comparisons, above `and`: `not X = Y` is `not (X = Y)`), `?`, `.Length`, `A[i]`, `T(k)` | ch. 4 |
| Failure | failure contexts (`if` conditions, `for` clauses, `option{}`, `logic{}`, `not`, left of `or`, `<decides>` bodies) with rollback of `var` writes **and output** (a `loop`'s body is none, also in a `<decides>` function, nor is a field's default: "`decides` is not allowed in `loop`", the Book's tests, `SOL-4199-BreakFromIf.versetest:79`, and ch. 13, [the rules](research/book-remaining-rules.md#a-loops-body-and-a-fields-default-are-no-failure-contexts); `--extended-defaults` keeps failing field defaults, which make a construction fail); an `if` condition, `logic{…}`, the operand of `not` and the left of `or` must be able to fail (the Book's tests refuse `not` of one that cannot, and an `or` whose left cannot, `LogicalOr.versetest:143`; its own `(set Map[I] = I) or Err()` has a failable left, a set through a map's key) | ch. 8 |
| Control | `if`/`else if`/`else` (all styles: the conditions in `(…)`, followed by a body or `then`; or as `{…}`, `:` and a block, or `.` and an expression, followed by `then` and a branch, or by nothing, which is the clause macro `if{c}` (see [Mutation, macros, tooling](#mutation-macros-tooling)): `if:`…`then:`, `if:`…`else:`, `if. c then. a else. b`; `for` likewise, with `do`), `for` with `X : array`, `I -> X : array`, `X := a..b` (`X:int := a..b` too), filters, bindings, several generators (cartesian product), and with none, failable clauses that run the body at most once (clauses of literals only, `for(X := array{1, 2})`, are refused: `X : array{1, 2}` iterates); each filter, a clause that is neither a generator nor a definition (`X := e`, `X:t = e`, `var X:t = e`), must be able to fail, as "Each filter must be failable" (ch. 7, `for.versetest:223`, [the rule](research/book-remaining-rules.md#every-filter-of-a-for-can-fail)): a print, a `set` or a call that cannot fail is refused as a filter, and goes with a check that can, as the Book's tests write it, `(set Temp = Element; true?)` (`for.versetest:233`), or in a definition's value or a generator's source, where effects stay among the clauses, or in the body; a clause with a choice in it, or a call of a function with several values, is a generator over their values (the Book has no choice: openverse's reading); a `for`'s clauses are one search, as the Book's tests have it (`FlowControl/for.versetest` 317-392): reaching the body keeps what they did since the last value, a failure undoes back to the element or alternative being tried, and what they did since the last value is undone when no more reaches the body, a source's or a range's bounds' included (which `for`s keep an older rule for now: [Readings](#readings-openverse-takes), "What a `for` undoes"), `loop`/`break` (a loop that nothing leaves, no `break` of its own and no `return`, is refused outside a `<suspends>` function, as the Book's tests have it, `Break.versetest` 117, 160, [the rule](research/book-remaining-rules.md#a-loop-that-nothing-leaves)), `return` (in a function's body: not in a constant's value or a field's default, which no function encloses; in a function whose result is not `void`, not a part of the value it returns: a `return` is the body's value, a branch of it or of a `case`, a `return`'s operand, or in code whose value is not returned, a block's other items, an `if`'s conditions or an `if` with no `else`, a `loop`, as the Book's tests have it, `Return.versetest` 114-162; `array{0, return A}` and `X + (return 0)` are refused), `profile(Tag): body`, `profile: body` and `profile{body}` (the tag a string, the value the body's; openverse measures nothing; not in an initializer, ch. 7, "Profiling"), `case` with literal patterns and `_` (an arm after `_`, or with an earlier arm's pattern, is never reached and refused, ch. 9; a `_` after every value of a closed enum is a [warning](#warnings)); code after a `return` or `break` that is never reached is a [warning](#warnings); no `return` or `break` leaves a failure context, as the Book's tests have it (`Reachability.versetest:12`, "Explicit return out of a failure context is not allowed"; `SOL-4199-BreakFromIf.versetest`): a `return` is refused in an `if`'s conditions, a `for`'s clauses (its body may return), `first`'s clauses, `option{…}`, `logic{…}`, `not`'s operand and the left of `or`, and, in a `<decides>` function, whose body is a failure context, anywhere but in tail position (`Return.versetest:157`: the body's last expression, the branches of an `if` with an `else` and the arms of a `case` in tail position, a block's last expression in tail position, a `return`'s value); a `break`, in those contexts between it and its loop | ch. 7 |
| Choice | `a \| b \| …` with several values in spatial order, in a clause of an `if` condition, `first{…}`, `option{…}`, `logic{…}`, `not` or `or` (the first success) or of a `for` (all of them), also inside expressions (`(1 \| 2) + (10 \| 20)`, `X = 1 \| 2`, `X > 0 and (1 \| 2)`, `M? or (1 \| 2)`); see [Choice](#choice) (#208) | (the Verse Calculus) |
| Functions | a parameter may be unnamed, `F(:int):void = {}`, as in function types (the body cannot name it; so may a parametric type's, `t(:type) := class{}`); a parameter may destructure a tuple, `Func(A:int, (B:int, C:int), D:int)`, to any depth: it is a parameter of the tuple type whose names the body sees (see [the rules](research/tuple-parameters.md); named parameters inside such a group are not supported); a tuple argument expands into parameters (`Describe(MyTuple)`); positional arguments pack into a single tuple parameter, including `tuple()` and singleton tuples; several arguments make a single array parameter (`Sum(1, 2, 3)`), including generic, overloaded, method and spawned calls (#134, #140, #501; nested fields retain their shape, and empty/singleton arrays use explicit array values); recursion, mutual recursion, `<decides>` (called with `F[…]`; other functions with `F(…)`; also `F of X` for `F(X)` and `F at X` for `F[X]`, the argument in braces `F of {42}`, a body after `:` or `.`, or an operand `F of array: …`, and a function defined `F of {I:int}:int = …`, the Book's tests, `Operators/Of.versetest`; `F at {…}` defines nothing), named parameters `?P:t = default` passed as `?P := e`, after the positional arguments (only a named parameter has a default, and a positional argument after a named one is refused, ch. 6, [the rules](research/book-remaining-rules.md#five-forms-the-tests-refuse)) (positional, then named as written, then defaults; a default may use the parameters before it, and a method's default the method's fields; a call dispatched to an override evaluates that override's own default for an omitted argument; a default is evaluated at the call and cannot return, break or use itself; it is its function's: it has only the heap effects the function allows and neither fails nor suspends, also of a `<decides>` or `<suspends>` function, checked once at the definition where the default can be elaborated in the function's scope, the Book's tests, `DefaultNamed.versetest` 805-878; `--extended-defaults` keeps openverse's reading, the default's effects the caller's, see [the rule](research/book-remaining-rules.md#a-named-parameters-default)), the heap effects `<computes>`, `<reads>`, `<writes>`, `<allocates>`, `<transacts>` (checked, see [Classes](#classes)), unsupported effect contracts are diagnosed before lowering (see [Effect contracts](#effect-contracts)) | ch. 6, 13 |
| Extension methods | `(R:t).M(…)<effects>:r = body`, at the top level, in a module or in a class, on a receiver of any type (`(:t)` unnamed; a `where` in its parentheses for a generic one), called `X.M(…)`, or `X.M[…]` when `<decides>`; overloaded by the receiver's type and the parameters', scoped like functions, never values; see [Extension methods](#extension-methods) | ch. 6 |
| Parametric functions | `F(X:t, … where t:type, u:subtype(comparable))`: type parameters in parameter types, the result type and local declarations; type arguments inferred at each call (see [Parametric functions](#parametric-functions)) | Types: where clauses |
| Structs | `name := struct:` with typed fields and defaults, `name{F := e, …}` (each field given at most once, evaluated in declaration order; separated by commas, or by `;` and new lines, not both; or as an indented block after `name:`, an archetype block; the type may be parenthesized, `(pair(int)){…}`; with `let:` clauses, whose definitions the field values after them see, and `block` clauses, which run where they are written and can neither fail nor `return`, the clauses and the field values run in the order written, ch. 10, "Let Clauses in Archetypes", [the rule](research/book-forms-rules.md#a-constructions-let-and-block-clauses)), `S.F`, `set S.F = e` / `op=` of a `struct<computes>` (ch. 5: "Only structs marked `<computes>` (pure structs) allow field mutation through a variable"; a path that reaches an object reads the structs before it, [the rule](research/book-forms-rules.md#a-structs-field-set)), structural equality (a struct is the tuple of its fields in Verse Core) | ch. 9 |
| Parametric structs | `pair(t:type, u:type) := struct:`, the type `pair(int, string)`, values `pair(int, string){First := 1, Second := "a"}` (or `pair{…}` where the expected type gives the type arguments); see [Parametric structs](#parametric-structs) | ch. 9 |
| Classes | `name := class:` and `name(t:type) := class:` with fields and methods; `class(parent, interface, …)` (`class()` has none, as `class`; a type `t()` or value `t(){…}` with no type arguments is `t`, `t{…}`), `interface`, `<abstract>`, `<override>`, `<final>`, `(super:)`, virtual dispatch, casts `T[X]` and `T(X)`, `var` fields; members in braces on one line separated by `,` or `;` (`class{X:int block{}}` is refused, as the Book's tests have it, `ClassBlockClause.versetest:19`); see [Classes](#classes) | ch. 10 |
| Enums | `name := enum:` / `enum{A, B}`, `name.A`, equality, `case` that needs no `_` when every value is named (an enumerator is its index in Verse Core); `enum<open>` may gain values, so a `case` on one needs `_` or a failure context (`<closed>` is the default) | ch. 9 |
| Maps | `[k]v` (a comparable key with no array or map in it, through its options, tuples and a struct's fields, but `string`: "neither may serve as a map key", ch. 3), `map{k => v, …}` (a key given twice keeps its last value, at its last position; a key cannot fail, ch. 3: "failure in map literal keys is not implemented"; [the rules](research/book-remaining-rules.md#map-keys-and-a-refinements-range)), `M[k]` (fails on a missing key), `set M[k] = v` (insert or update; in Verse the key's reference is `<decides>`, the Book's API reference, so such a `set`, also as a path's last step, `set S.M[k] = v`, is written in a failure context, as the Book's tests do, `if (set M0[0] = 42)`, `(set Map[I] = I) or Err()`; its last key inserts, so it succeeds; its value is `v`), `set M[k] op= v` (fails on a missing key), `.Length`, `for (V : M)`, `for (K -> V : M)` in insertion order, `ConcatenateMaps(M1, M2)` (exactly two maps, ch. 3: more by chained calls; their pairs laid down in turn, as `map{…}` lays its own: a key both maps have takes the second map's value at the second map's place, the Book's API reference and `ConcatenateMaps.versetest` 21, 33), order-sensitive equality (a map is the array of its pairs in Verse Core); a key of a class above or beside the map's key class reads, looked up at the class above both; `weak_map(k, v)`, a supertype of `[k]v` with entry access only (see [Weak maps](#weak-maps)) | §3, §9.3 |
| Array methods | (also of a tuple of one element type, which is an array where one is expected: `('a', 'b', 'c').Slice[1]`) `A.Slice[i, j]`, `A.Slice[i]`, `A.Find[x]`, `A.RemoveElement[i]`, `A.RemoveFirstElement[x]`, `A.Remove[i, j]` (half-open), `A.ReplaceElement[i, x]`, `A.ReplaceFirstElement[x, y]`, `A.Insert[i, B]`, `A.Last[]`, `A.Last[n]` (the element n before the last) (all failable); `A.RemoveAllElements(x)`, `A.ReplaceAllElements(x, y)`, `A.ReplaceAll(Pattern, Replacement)` (contiguous subarrays, left to right, not overlapping; an empty pattern changes nothing), `Concatenate(A, B, …)` or `Concatenate(Arrays)` (#150) (never failing) | §9.1 |
| Built-ins | `Print(s)`, `ToString(x)` (int, float, char, char32, string), `Floor[F]`, `Ceil[F]`, `Round[F]`, `Int[F]` (of a float, failable), `Floor(R)`, `Ceil(R)` (of a rational or an int, never failing; `Floor(X / Y)` fails when `Y = 0`, as `X / Y` does), `Quotient[X, Y]`, `Mod[X, Y]` (Euclidean), `Abs`, `Min`, `Max`, `Clamp(Val, A, B)` (the median of the three, of ints or of floats, NaN ordering above +Inf), `Sgn(X)` (-1, 0 or 1 of an int or a float, NaN of NaN), `F.IsFinite[]` (as `IsFinite[F]`), `BitAnd(X, Y)`, `BitOr`, `BitXor`, `BitNot(X)`, `BitShiftLeft[X, N]`, `BitShiftRight[X, N]` (see [Bitwise functions](#bitwise-functions)), `Err()` and `Err(Message)` (stops the program; ch. 8: "a runtime error with an optional message", the API reference `Err(Message:string)`: no argument or one string, which is evaluated first); a built-in given another number of arguments than it takes is refused (`Quotient takes two ints, found 3 argument(s)`); the conversions of chars and code points as methods (see [char32](#char32)): `C.ToCodeUnit()`, `C.ToAsciiChar32[]` of a char, `C.ToCodePoint()`, `C.ToAsciiString()` of a char32, `N.ToChar[]`, `N.ToChar32[]` of an int | API reference |
| Modules | `name := module:` (nested), `M.F`, `A.B.F`, the types `M.c` and values `M.c{…}`, `(M:)F`, `using{M}` at file or module scope (a `using` of a path is accepted and ignored, but of `/localhost` and the paths below it, which the Book's tests refuse, "Explicitly using a "/localhost" package is not allowed", `Modules/Using2.versetest` 84-90), `<public>` members (`<internal>` is the default); see [Modules](#modules) | ch. 16 |
| Access | `<public>`, `<internal>` (the default), `<protected>`, `<private>`, `<scoped{M, …}>` and `S := scoped{…}`, `<epic_internal>`, on modules, their definitions, a class's members and constructor, and `var<w> X<r>:t`; checked where each use is written, and no definition exposes a less visible one; see [Access](#access) | ch. 12 |
| Attributes | `@deprecated`, `@experimental`, `@available{MinUploadedAtFNVersion := N}`, custom attributes (a class below `attribute` with its scopes `@attribscope_…`, `@c{F := e}` or a constructor's `@f(…)`) before a definition, a member, a struct's field or an enum's value; `@ignore_unreachable` on an expression or a `case` arm: checked where the Book checks them, metadata but `@available`; see [Attributes](#attributes) | ch. 12 |
| Qualified names | `(M:)x`, `(c:)m`, `(e:)v`, `(local:)X`, `(/Verse.org/Verse:)int`, in uses and in definitions' heads: a qualifier names a scope, the name is looked up in exactly that scope, and a definition's qualifier names where it is defined; see [Qualified names](#qualified-names) | ch. 9, 10, 16 |
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
- A `.` and what follows it, a member (`O.F`) or a dot form's body
  (`if (C). E`), are on one line with no comment between them: `O. F` and
  `O<#c#>.F` are `O.F`, and `O.` at the end of a line or before a comment
  is an error, as the Book's tests have it (`ReserveDotSpace.versetest`
  3-7, [the rule](research/book-forms-rules.md#a--and-what-follows-it)).

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
`local`, `true` and `false`, and the effects' names, `suspends`, `decides`,
`varies`, `reads`, `writes`, `allocates`, `computes`, `converges` and
`transacts`, which the Book's tests refuse as definitions' names, qualified
or not (`Enum.versetest`, `Effects.versetest`); and the names the Book's tests reserve for the future
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
`when`, `while`; and `of` and `at`, which call a function (`F of X`, `F at
X`), and which a test calls "The 'at' reserved word"
(`SemicolonsVsCommas.versetest:52`). openverse reads `first`, `assert` and `let` as macros
before `{` or `(`, and `using` is a keyword. A qualifier does not lift the
rule (`(m:)local` is refused), but an enum's value qualified with its enum
may take any name, a keyword's too ([Qualified names](#qualified-names)),
and only qualified may it take one of these or an access specifier's name
(`public`, `internal`, `protected`, `private`, `epic_internal`): `enum{
public }` is refused, `enum{ (A:)public }` is not (ch. 9: "Qualification
also allows you to use reserved words and keywords as enum values, which
would otherwise cause errors"; `QualifiedIdentifier.versetest` 313-316). The function type
`type{_(:int):int}` writes `_` as no definition's name, and stays allowed.

No definition takes a built-in type's name either (`typeNames` in
`Front/Syntax.lean`): `int`, `logic`, `char`, `char32`, `string`, `void`,
`float`, `rational`, `any`, `comparable`, and the metatypes' `type`,
`subtype` and `concrete_subtype`. A type (`int := class{}` or a type
alias: "int is a built-in type"), a constant, a module, a type parameter, a
parameter, a local and a field are refused alike: the built-in types are
definitions every scope sees (ch. 16, "Automatic Qualification": `int` is
`(/Verse.org/Verse:)int`), no definition takes the name of one around it
(ch. 10), and a use of the name would read the type. A function or a method
may take one, as the program's own, which its calls reach (`any(X)` calls a
function `any` the program defines), and so may an enum's value, used
qualified. The Book's tests reserve `subtype` and
`castable_subtype` in every place (`Subtype.versetest` 229-242), `true`
(`Enum.versetest:59`) and a local `array` (`Array.versetest:96`, a keyword
in openverse), and define nothing named like another built-in type. The
names of the library's types that a program may define itself, `event`,
`task` (a local `task`, `Super.versetest:35`), `weak_map`, `message`, are
the program's where it does.

## Parametric functions

A function with a `where` clause is generic. The clause ends the parameter
list and declares each type parameter as `t:type`,
`t:subtype(comparable)`, or with an upper bound, `t:subtype(vehicle)` (see
"Upper bounds" below):

```verse
Find(Items:[]t, Target:t where t:subtype(comparable))<decides>:int = ...
Combine(A:t1, B:t2 where t1:type, t2:type):tuple(t1, t2) = (A, B)
```

- **Checked once.** The body is type-checked once, with every type parameter
  opaque. A value of type `t` can be bound, passed, returned, stored in
  arrays, options, tuples and maps, and iterated over in a `[]t`. `=`, `<>`,
  `Find` and map keys need `t:subtype(comparable)`; compared with a value of
  another type, or converted to `comparable`, a `t` is boxed by its
  instance's box, which a function that needs it takes as one more hidden
  argument, the evidence of `t:subtype(comparable)` ([comparable](#comparable));
  every other generic function takes none. Anything else, such as
  arithmetic, `ToString` or `.Length` on a bare `t`, is a type error, even if
  the function is never called.
- **Every type parameter is given by the parameters** (the Book's tests,
  `ParametricFunctions.versetest` 336-378 and 586, error 3503): it is named
  in a parameter's type where values go in, or in the result's at a place
  values go in (a function type's parameter, `G(N:int where t:type):(t->void)`),
  or in the bound of one that is (`Up(X:t where t:subtype(u), u:type)`). A
  function type's parameter is no such place (`Apply(F:t->void where
  t:type)` is refused: a value of type `t->void` takes any `t` below one in),
  nor is a class's or interface's type argument where it only takes values
  in, a contravariant one (`Use(S:sink(t))` with `sink(t) := class{Take(X:t):void}`:
  any `sink(u)` below it is one); a class that does not use its type
  parameter gives it (the Book is silent; an object holds its type
  arguments). The result alone gives none: `Make(N:int where t:type):?t` is
  refused, where it is declared, and a program writes the type as an
  argument instead, `Make(t:type):?t` called `Make(int)` (the Book's
  `MaybeValueExplicit(t:type, Value:t, Valid:logic):?t`, ch. 2), or a
  result `false` for a function that never returns. The compiler's own
  functions (whose names have `$`) keep the old reading, their calls being
  the compiler's.
- **Inferred type arguments.** At a call, the result type is matched against
  the expected type (unless that is `void`), then each parameter type against
  its argument's type. Arguments are matched left to right, except that
  `false`, `array{}` and `map{}` are matched last, because they take their type
  from context; a `false` (an argument's or a default's) whose type nothing
  else gives is a `logic`, as `X := false` is (`Id(false)`, as the Book's
  `Identity(true)`, is at `logic`). A type parameter that is still unknown
  is an error. Arguments are still evaluated left to right.
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
- **Upper bounds** (#502, Book of Verse ch. 6, "Type Constraints" and
  "Member Access"). `t:subtype(c)` takes as `t` any subtype of `c`, and
  the function sees a `t` as a `c`: `Process(X:t where
  t:subtype(vehicle)):t` reads `X.Speed` and calls `X.Describe()` (the
  instance's override), and `Process(car{})` is a `car`. A bound may be a
  class or an interface, a parametric one applied (`subtype(box(int))`),
  another type parameter of the clause (`u:subtype(t)`), `rational`, a
  refinement type, an array, option, tuple or map type (`subtype([]rational)`
  with a `[]int`: indexing, `.Length`, `?`, the array methods, iteration
  and projections read through it), a function type (a `t` is then called),
  `any` or `void`; and `t:castable_subtype(c)` asks for a `<castable>`
  subtype of `c` (Book's tests, `Castable.versetest` 510-603). A class's,
  interface's or struct's type parameter takes a bound too
  (`holder(t:subtype(vehicle)) := class`). The instance is checked at every
  call, construction and written type application, also in a type alias's
  type and a class's parents, where it is defined; a bound's facts make a
  call of another bounded function with `t` valid. Each bound is one more
  hidden argument, checked evidence that the instance is below the bound
  (an upcast, or the conversion of `int` to `rational` or of each element of
  a container), which the function's operations on a `t` use; no evidence is
  made from a type alone ([upper-bound evidence](research/upper-bound-evidence.md)).
  Refused, each by a rule of its own: an instance outside the bound (the
  Book's 3509); a bounded type parameter, or one a bound names, that no
  parameter's type determines (`Foo(X:int where t:subtype(u), u:type):?t`,
  3503; one without a bound too, above); a
  public parametric type whose bound is less visible (3593); several bounds
  on one type parameter (the Book: "not yet supported"); `concrete_subtype(c)`
  as a bound; a cast of a bounded `X` (`i[X]`: the Book's
  `FORT-1059276.versetest` refuses it, `Y:c = X; i[Y]` is the way); a write
  through a container upper (`set X[0] = …` with `X:t`,
  `t:subtype([]rational)`: no conversion back to `t` exists); a cast to or
  a construction of a type parameter (`t[X]`, `t{}`); and variance of a
  function object already made (a bound does not make
  `type{_(:car):int}` a `type{_(:vehicle):int}`).
- **Limits.** A generic `Main`, several constraints on one type parameter
  (also unsupported in the Book), type arguments written at a call other
  than for a parameter `t:type`, `t:subtype(c)` or `t:castable_subtype(c)`
  the function uses as a type (`F(t:type,
  X:t)`, called `F(int, 3)`: [Types as values](#types-as-values), "A type
  given as an argument"), and generic constants are not supported.

## Effect contracts

The supported effect vocabulary is `computes`, `reads`, `writes`, `allocates`,
`transacts`, `decides` and `suspends`. Function declarations and function types
reject duplicate or contradictory effects, and reject unknown execution
specifiers before lowering can erase them (#494). They also reject a redundant
one, as classes, interfaces and structs do: `<transacts>` implies `<reads>`,
`<writes>` and `<allocates>` (ch. 13), so `<transacts><allocates>` is refused.
`<converges>`, `<computes>` and `<transacts>` exclude each other; `<reads>`,
`<writes>` and `<allocates>` are additive, also with `<computes>`:
`<computes><allocates>` allows allocating and nothing else of the heap
(ch. 13: "A function may have at most one exclusive specifier but can
combine multiple additive ones"; `Attributes/allocates.versetest` 4-32).

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
and callers (#508). No heap annotation means `transacts`; `computes` alone
permits none; `reads`, `writes` and `allocates` permit those named, also
with `computes` (`class<computes><allocates>`). A subtype must
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
OpenVerse's reading of defaults from before the Book's tests pinned theirs,
and exactly three things of it (`Options.extendedDefaults`): field defaults
that compute anything, ordinary helper/callback and spawn defaults included,
with no convergence assertion; field defaults that can fail, which make the
construction that omits them fail ([the
rule](research/book-remaining-rules.md#a-loops-body-and-a-fields-default-are-no-failure-contexts));
and named parameters' defaults that have the caller's effects rather than
their function's (failing in a failure context, waiting in a `<suspends>`
caller; the Book's tests refuse them, [the
rule](research/book-remaining-rules.md#a-named-parameters-default)). Heap,
failure, suspension, source-profile and Core checks still apply at each
call. Compiler clients use
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
| `<final>` | a class, a method or a field, a struct's included (not an interface, a struct, a module's function) | a method's body, a field's value; no class below overrides a `<final>` field and no construction gives it a value |
| `<final_super>` | a class | a parent, a class or an interface (ch. 10, "Final"; the tests' 3679) |
| `<final_super_base>` | a class or an interface | a class right below it is `<final_super>` |
| `<castable>` | a class or an interface | no type parameters, nor in a class or interface below it |
| `<unique>` | a class or an interface | |
| `<persistable>` | a class (not supported yet), a struct or an enum | a struct's: no type parameters, and fields that persist: not `any`, a rational, a function, an interface, a class, or a struct or an enum that is not `<persistable>` (ch. 17: "Enums without `<persistable>` specifier cannot be used") |
| `<override>` | a method or a field | |

Anywhere else, on a definition's name (`c<castable> := class{}`) or after the
keyword of another kind (`interface<abstract>`, `struct<final>`), each is
refused. Enums take `<open>`, `<closed>` and `<persistable>`; access
specifiers go where [Access](#access) says, in the same table; a specifier
that is no keyword openverse knows and names no access level
(`<intrinsic>`) is refused; and effects are the subject of the rest of this
section.

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
  named arguments run as written before omitted defaults. A qualified local
  or field (`(local:)F`, `(c:)F`), or a method a call can tell apart from
  it, keeps its meaning when a generic top-level function has the same name.
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
  parameters: `A(F(:int):int, X:int):int`. Not supported: named parameters
  inside a tuple parameter, and tuples with named elements (a named
  parameter with its function's name, `F(?F:int)`, is refused as a
  shadowing). See the
  [pinned rules](research/named-function-values.md).
- A built-in function of one signature is a function like any other: named
  as a value (`CheckSpecials[Sin, NaN, NaN]`, as the Book's tests write), it
  is a value of its type and effects: `Sqrt`, `Exp`, `Ln`, `Sin`, `Cos`,
  `Tan`, `ArcSin`, `ArcCos`, `Pow`, `Log` (`<computes>`), `Sinh`, `Cosh`,
  `Tanh`, `ArSinh`, `ArCosh`, `ArTanh`, `Lerp` (`<reads>`), `IsFinite`,
  `Round`, `Int` (`<computes><decides>`), and the bitwise functions
  `BitAnd`, `BitOr`, `BitXor`, `BitNot` (`<computes>`), `BitShiftLeft`,
  `BitShiftRight` (`<computes><decides>`). The program gets an ordinary
  definition of the built-in, which calls it, unless it defines or binds
  that name itself. The others are no values: overloaded (`Abs`, `Min`,
  `Max`, `Floor`, `Ceil`, `ArcTan`, `Clamp`, `Sgn`, `ToString`), generic
  (`Concatenate`, `ConcatenateMaps`) or names a program cannot define
  (`Quotient`, `Mod`, `Print`, `Err`).
- Extension methods cannot be used as values ([Extension methods](#extension-methods)).
- Overloaded functions and methods cannot be used as values (Book of Verse
  ch. 6, "Capture"), with or without named parameters. Local function
  declarations and lambda expressions are unsupported. The pinned Book marks nested functions unreleased and arrow
  lambdas unsupported; this is not a versioned UEFN compatibility result.
  See the [closure design and release evidence](research/closure-design.md)
  for the proposed capture/lifetime rules and implementation gates.

## Extension methods

An extension method adds a method to a type without changing the type
(Book of Verse ch. 6, "Extension Methods"; the rules, quoted with the
Book's tests, are [pinned here](research/extension-methods.md)):

```verse
(Value:int).Double()<computes>:int = Value * 2
(Text:string).Wrap(Open:string, ?Close:string = ">"):string = "{Open}{Text}{Close}"
(Xs:[]t where t:subtype(comparable)).Count(Y:t):int = …
Main():void =
    Print("{7.Double()} {"a".Wrap("<")} {array{1, 2, 1}.Count(1)}")   # 14 <a> 2
```

- **One rule.** `(R:t).M(params)<effects>:r = body` is the function
  `$ext:M(R:t, params)<effects>:r = body`: an ordinary function whose first
  parameter is the receiver, under a name no program can write. So `M(X)`
  does not call it and `X.M` is no value of it ("Extension methods must be
  called"), and everything else is a function's: overloads, told apart by
  the receiver's type and the parameters' by the rules of
  [Overloading](#overloading) (`(A:[]int).F()` beside `(A:[int]int).F()` is
  refused: the empty map is an array); a `where` in the receiver's
  parentheses or after the parameters; named parameters and defaults; a
  tuple argument spread over the parameters after the receiver
  (`Origin.Translate(Delta)`); effects, `<decides>` and the `[…]` it needs;
  several values (`(I:int).Around():int = I - 1 | I | I + 1` in a `for`);
  `<suspends>` and `spawn{X.M()}`.
- **The receiver** is one parameter, named or not (`(:t)`), of any type: a
  scalar, a string, a tuple (`tuple(int, int)`, `tuple()`), an array, a map,
  an option, a class, an interface, a struct, an enum, a type parameter.
  Two parameters, `(A:int, B:int).M()`, none, `().M()`, a named one and a
  default are refused, and so is `(R:t).M:t`: there are no extension
  fields. `M` cannot be a [reserved name](#reserved-names).
- **Scope.** A call `X.M(…)` finds `$ext:M` as a function's name is found
  ([Modules](#modules)): in the call's module and those around it, innermost
  first, then in the modules they open with `using`, `<public>` ones from
  outside. The call is then `$ext:M(X, …)`, `X` evaluated once, before the
  arguments. An extension method in a class is a method of the class, a
  closure over `Self`'s fields (`game_manager`'s `(Score:int).Scaled()`
  reads its `Multiplier`), which the class's methods call as `X.M(…)`.
- **The receiver's own members.** When `X`'s type has a member `M` of its
  own (a field, a method, inherited ones included, a built-in method of an
  array, a char, a number or a task), the call is the member's, unless only
  the extension method fits the call; one that fits both is refused as
  ambiguous, as two overloads would be. So a field `Q` of one class and an
  extension method `Q()` of another meet nowhere, `box{}.Put(1)` calls the
  method `Put(I:int)` and `box{}.Put("a")` the extension `(B:box).Put(S:string)`,
  and an extension method on a class `c` and the method of a class below
  `c` that a call fits both are ambiguous. An extension method on a class
  or an interface with the parameters of one of its methods, own or
  inherited, is refused where it is defined (the Book: "cannot have the
  same signature as methods defined directly in classes or interfaces"),
  and so is one on an array, a string, a char, a char32, an int or a
  float with the parameters of that type's own method of its name
  (`(A:[]int).Find(X:int)`, `(N:int).ToChar()`), whatever its effects; one
  with other parameters (`(A:[]int).Find(X:string)`) is an overload.
- **In a method**, a bare call `M(…)` whose name an extension method in
  scope has is `Self.M(…)` when only the extension method fits it with
  `Self`; otherwise it keeps its meaning, and it is ambiguous when both fit
  (the Book's tests: a function `DoSomething2()` and an extension method
  `DoSomething2` of `Self`'s class).
- **Static.** The extension method a call takes is chosen by the
  receiver's static type, and nothing overrides it.
- **Built-in methods.** The conversions of chars and numbers are extension
  methods in the Book's Runtime API (`(Byte:char).ToCodeUnit()`), and the
  array methods are "the array extension `Last`" (ch. 16). They are members
  of their receivers' types here, compiled inline as before, so a program's
  extension method of their name applies to other types, and one that takes
  the same receiver makes a call ambiguous.
- **Qualified.** `X.(M:)F(…)` calls the module `M`'s extension method `F`,
  where several are in scope ([Qualified names](#qualified-names)).
- **Not supported:** a qualified extension method's definition,
  `(P:player).(M:)F()`, and one a path qualifies,
  `(P:player).(/Verse.org/M:)F()`; `<override>` on one,
  which the Book does not describe; the receiver typed from its context
  where it has no type of its own (`map{}.RemoveKey[0]` for a generic
  `(Input:[int]u where u:type)`).

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

No `return` or `break` can leave a failure context ([Control](#supported),
the Book of Verse's tests): a `defer:` runs at one that leaves its scope from
a branch or a block, and a new local loop keeps its own target even inside
a lifted branch. Breaks in a body's own `loop` stay local; a `for` body
itself is not a break target.

## Overloading

Several functions may share a name when no call could fit two of them (Book of
Verse ch. 6): `Describe(X:int)`, `Describe(S:string)`, `Describe(X:int, Y:int)`.
Nothing else shares a name in one scope (the top level or a module): two
classes, interfaces, structs, enums or constants of one name, or one of them
and a function (`c := class{}` with `c(I:int):c`, which the Book's tests
refuse as "overloading a class"), are a name defined twice. A local cannot
take an overloaded function's name either.
- **Operators.** A program may overload the operators `+`, `-`, `*`, `/`
  and prefix `-` at the top level, as functions written
  `operator'+'(L:vec2i, R:vec2i):vec2i = …` and `prefix'-'(V:vec2i):vec2i =
  …` (overloads of one another as any functions are). An operator whose
  operand the built-in one does not take (no int, float, rational,
  refinement or, for `+`, array) calls the overload the operands fit, with
  brackets when it is `<decides>` (`operator'/'(L:vec2i, R:int)<decides>`
  makes `V / 0` fail); `-3 + 1` stays the built-in's. Other operators
  (`operator'()'`, the comparisons, `+=`) are not overloadable (the Book's
  tests, `Overloading.versetest` 196-232).
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
  so are one parametric class's instances at disjoint type arguments, and a
  type as a value, of `type` or a metatype, `subtype(c)`, and an object of
  a class: `F(:subtype(c))` and `F(:d)` are two overloads). Function
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
- **Extension methods** overload as functions do, the receiver their first
  parameter ([Extension methods](#extension-methods)); a call takes one of
  them or the receiver type's own member of the name, whichever it fits.
- **Constructors.** Constructor names may overload, including generic
  constructors, defaults and delegation. The arguments select one overload.
- **Entry point.** `Main` must have one definition under the OpenVerse CLI's
  entry-point policy. This is separate from ordinary Verse overload rules.
- **Argument shapes** (#501). Calls pack their arguments into a single
  tuple or array parameter, explicit or generic, overloaded calls included,
  and a tuple argument that does not fit a one-argument overload can
  expand into a different overload's positional parameters; its receiver
  and producer are evaluated once, before named arguments and defaults. The
  [pinned conformance audit](research/overloading-conformance.md#call-packing-501)
  records reproducers, diagnostics, source rules and regression links.
- **Bounds** (#502). Overloads whose bounds are disjoint sibling classes
  (`t:subtype(car)` and `t:subtype(truck)`) are distinct; an interface
  bound overlaps every class (a class below both may come), and so do an
  ancestor and its descendants and the empty containers.

## Parametric structs

A struct with parameters is a family of struct types:

```verse
pair(t:type, u:type) := struct:
    First:t
    Second:u

Swap(P:pair(t, u) where t:type, u:type):pair(u, t) =
    pair(u, t){First := P.Second, Second := P.First}
```

- A parameter is `t:type`, `t:subtype(comparable)` or an upper bound,
  `t:subtype(c)` ([Parametric functions](#parametric-functions), "Upper
  bounds"). The field types and
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
    container first, as `set A[i] = e` does. A path may start at a call's
    result or a construction, `set F(Y, X).Contents = Y.Contents`, `set
    c0{}.X += "def"`: the root is evaluated first, then the keys, then the
    value (the Book's tests, `AssignmentSequencing.versetest` 17-48); a key
    of several values is a tuple's, `set M[1, 2] = 1` (`Map.versetest:472`).
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
  interfaces; no parent is named twice (an interface inherited again
  through another parent is inherited once, but `class(i, i)` and
  `interface(i, i)` are refused, the Book's tests, `Interface.versetest:31`,
  [the rule](research/book-remaining-rules.md#an-interface-named-twice)).
  Interfaces may declare fields, with or without defaults, and methods,
  with or without a body (a default). An interface below another inherits
  its members and may add its own, but overrides none: `<override>` in an
  interface is refused, and so is a member it inherits declared again, with
  a new body, value or type or without (the Book's tests,
  `Interface.versetest:193`, "Interfaces can not override anything";
  `InterfaceWithFields.versetest:312`, "Can't override in an interface";
  `InterfaceDiamond.versetest:89`, 3523, 3532). A class below gives an
  inherited member its implementation or a new default. A
  class inherits its parent's fields, then those of the interfaces above it
  that are not there yet (once, along a diamond), then its own, and its
  methods:
  - `Name<override>:t = e` gives an inherited field a new default, and
    `Name<override>:t` re-declares it with none, so that a construction
    gives it (the Book's tests, `Attributes/override.versetest` 29-47); any
    other field with an inherited name is an error;
  - a class may re-declare a field that is no `var` at a type below the one
    it inherits (ch. 10, "Overriding Members": "fields can only be
    overridden with subtypes"): `Pet<override>:cat` over `Pet:animal`,
    `Kind<override>:int` over `Kind:comparable` or `any`, a refinement over
    its base, `tuple(int, int)` over `[]int`. Read through that class or one
    below it, the field has the narrower type; through a class or interface
    above, the inherited one. A `var` keeps its type (a write through a
    class above could store a value of the wider one);
  - `M<override>(…)` overrides an inherited method with its signature, except
    that it may return a class below the declared one (covariant results).
    Overriding without `<override>`, or `<override>` that overrides nothing,
    is an error;
  - `<final>` methods cannot be overridden, and `<final>` classes cannot be
    inherited from;
  - `(super:)M(…)` calls the implementation inherited from above, of `M`
    or of another overload of `M`, and is written only in the code of an
    `<override>` of `M` (its body, a block or a `spawn` in it, its
    parameters' defaults): not in another method, a class's `block:`, a
    field's default or a function (the Book's tests, `Super.versetest`:
    "super on another method", "Calling `(super:)` from blocks is not
    allowed", 3612).
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
    class: the nearest in its class chain, else the default of the
    interface that declares the method, whatever order the parents are
    listed in. This is virtual dispatch, also inside a method; `(super:)`
    uses the same rule.
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
    and inside a method a bare `(i1:)M()` is `Self.(i1:)M()`. The qualifier
    names the class or interface that introduces `M`: one that inherits or
    overrides it is refused ([Qualified names](#qualified-names)). A call through
    a type whose slots some class below implements differently is refused as
    ambiguous, so every static path to a slot reaches the same code.
  - **`(super:)M()`** in `(r:)M` is slot `r`'s implementation above. In a
    plain `M` it is refused when the slots above differ.
  - **Restrictions.** A class gives `M` plainly or qualified, not both. A
    plain `M<override>` in a subclass implements all its slots. `(c:)M` in
    class `c` itself is `M`, unless a class above has an `M`: that would be
    a second method `M`, which openverse refuses.
- **Fields with accessors** (Book of Verse ch. 10, "Fields with
  Accessors"; ch. 12, "Getter and Setter Accessors"; the rules and their
  sources are pinned in [research/accessors.md](research/accessors.md)).
  `var X<getter(G)><setter(S)>:t = external{}` in a class or an interface
  is a field with no storage: a read of `O.X` (or of `X` in a method) is
  `O.G(…)`, a `set O.X = v` is `O.S(…, v)`, whose value is `v`.
  - **Declaring.** One `<getter(…)>` and one `<setter(…)>`, on a `var` of a
    class or an interface (not a struct); the default `external{}` or none,
    and then every construction gives the field. `G` and `S` are methods of
    the class or of one above it (a method of an interface is one), each
    taking first an unnamed parameter of the type `accessor`:
    `G(:accessor):t` and `S(:accessor, V:t):void`, at the field's type
    exactly; their other overloads read and set paths (below). Not of a
    tuple type (the Book's tests).
  - **Overriding.** A field with accessors is not overridden, and its
    accessors are not overridden below the class or interface that declares
    it. A class may give a field with storage of a class or interface above
    it accessors, `var X<override><getter(G)><setter(S)>:t = external{}`:
    its objects then read and set `X` through them, also through the type
    above, where the object's class decides (a test of it, as for a field at
    different places).
  - **Paths.** `O.X[I]`, `O.X.F[J]`: a path into the field's value, up to
    the first object in it, is one call of the overload of `G` (or of `S`,
    for a `set`) that takes, after the accessor, the path's indices and the
    names of the struct fields it goes through, as strings, then for `S` the
    value: `GetX(:accessor, I:int)<decides>:int`. Such an overload must
    exist; one that can fail is used in a failure context. A path that goes
    on into an object reads the field with `G`, then goes on in the object;
    `O.X.Length` reads `O.X`.
  - **Order.** `O`, then the indices, then `v`; for `set O.X op= v`, then the
    old value through `G`, then `S`. A construction evaluates its fields'
    values in the order they are declared, those with accessors among them,
    makes the object, calls the setters of the fields with accessors it
    gives, in that order, then runs the `block:` clauses.
  - **Access.** A use of the field is judged by the field's access (and its
    `var`'s for a `set`), not by its accessors': a `<public>` field may have
    `<private>` accessors. The accessors cannot be called otherwise, since
    no program can make the value of their first parameter.
  - **Not supported:** a constructor function that gives a field with
    accessors; a path into such a field's value through a type above a
    class that gives a field with storage accessors.
- **Casts.** `T[X]` is `X` as a `T`, failing unless `X`'s class is below
  `T`. `T(X)` converts to a supertype and cannot fail. A cast to a class or
  interface that no class of `X`'s is below compiles and always fails, with
  a [warning](#warnings) (ch. 11: "These casts succeed and return the
  casted value, failing if the value is not of" the type; the Book's tests
  accept them, `Interface.versetest:150`); one to a parametric class or
  interface whose type arguments no class below both can give is refused
  ("would always fail").
- **Final super classes** (Book of Verse ch. 10, "Final"; ch. 11,
  "final_super and Type Queries"; the API reference; the rules are in
  [research/classes-and-subtyping.md](research/classes-and-subtyping.md#final-super-classes)).
  A `<final_super>` class has a parent, a class or an interface; a class
  right below a `<final_super_base>` class or interface is `<final_super>`.
  `GetCastableFinalSuperClass[B, X]` gives, as a `castable_subtype(B)`, the
  class that is `<final_super>`, castable (`<castable>` or below a
  `<castable>` class or interface), right below `B` (a parent of its), and
  `X`'s class or above it, and fails when there is none; of the classes
  that list an interface `B`, the topmost. `X` is of the type `B`.
  `GetCastableFinalSuperClassFromType[B, T]` does the same for the class
  the type value `T` holds (any type: one that is not below `B` makes it
  fail). `B` is a type written at the call; one that is no class or
  interface (`int`, `any`) makes the call fail, and its result is then a
  `type`. Both are `<reads><decides>`; a program may define functions of
  these names, which its calls then call.

  ```verse
  component := class<castable>{}
  physics := class<final_super>(component){}
  rigid := class(physics){}
  if (T := GetCastableFinalSuperClass[component, rigid{}]) then
      Print(if (T[physics{}]) then "physics" else "?")      # physics
  ```
- **Parametric classes.** A parametric class is a reference like any other
  (#39): `stack(t)` can have `var` fields, be `<unique>`, and refer to
  itself (`node(t) := class: Value:t; var Next:?node(t) = false`), in its
  fields only at its own type parameters, in order: `Next:?node(?t)` or,
  for `bi(t, u)`, `Next:?bi(u, t)` is refused, and so are two parametric
  classes or interfaces whose fields name each other, directly or through
  others (Book of Verse ch. 10, "Disallowed: Polymorphic Recursion",
  "Disallowed: Mutual Recursion"; classes without type parameters may name
  each other). It can be
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
  generic over `container(u)` reaches it with `u` as `[]t` (#53). An
  interface without type
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
- **Variance** (Book of Verse ch. 10, "Instantiation and Identity";
  [research/variance.md](research/variance.md)). A parametric class's or
  interface's instances convert to one another by the use of each type
  parameter in its members, inherited ones included: only where values come
  out (a field that is no `var`, a method's result) it is *covariant*, and
  `producer(player)` is a `producer(entity)`; only where they go in (a
  method's parameter) *contravariant*, and `consumer(entity)` is a
  `consumer(player)`; in both, or in a `var` field, *invariant*; nowhere,
  *bivariant*, and any instance is any other. A type argument of another
  class counts by that class's variance there, a function type's
  parameter contravariantly (so `Each(F:type{_(:t):void})` is covariant in
  `t`), arrays, options, tuples and maps covariantly; a use only at a
  bivariant position of the class itself is none. The conversion keeps the
  value (a class is a reference), so a type argument must be one of the
  other as it is: a class below, a refinement of it, `comparable` for a
  value that is its own box; not `int` to `rational`, nor anything to `any`,
  which holds no value in openverse. Joins go by variance too: two
  instances of a covariant class join at the instance at their type
  arguments' join, of a bivariant one at either.

  ```verse
  producer(t:type) := class:
      Value:t
      Get():t = Value
  EntityProducer:producer(entity) = producer(player){Value := player{}}
  ```

  openverse needs more than the Book in one respect: Verse Core types a
  reference by its object's *own* class (a method runs at the reference's
  type arguments), so every concrete class below the converted type must
  allow the conversion too, by its fields alone (methods are free there:
  Verse Core has no contravariance, and a class whose fields do not use a
  parameter is bivariant in it). So a conversion is refused, with a
  message that names the class, where a class below the type (or the type
  itself) holds the parameter in a field and the conversion is
  contravariant or bivariant (an implementation `store(t)` of a
  contravariant `sink(t)` with a field `Last:t`: no `store(entity)` is a
  `sink(player)`), writes a field of it (`var`, also one a subclass adds:
  no `rw(player)` is a `ro(entity)` when `rw` adds `var W:t`), fixes it
  and overrides one of the type's methods or is the target of a refining
  cast (`pp := class(producer(player))` with `Get<override>`), or sees it
  through an interface referred to through views (#351). Function types
  convert as before (#214).
- **Heap effects** (#35). A
  function's specifiers allow a set of heap effects: all of them when it has
  none or `<transacts>`, none with `<computes>` alone, and those named by
  `<reads>`, `<writes>` and `<allocates>` (with `<computes>` or not). Reading a `var` field *reads*,
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
  - variance where a class below the converted type holds or writes the
    type parameter in a field, fixes it and overrides or is cast to, or
    sees it through a view (see [Variance](#classes) above): Verse Core
    types a reference by its object's own class
    ([research/variance.md](research/variance.md)); and a type argument
    inferred through a variant position (`F(C:c(t), X:t)` takes `t` from
    its first argument, as without variance);
  - a method override at a signature that needs a conversion (a result
    `tuple(t, t)` for `[]t`, parameters `(X:int, Y:int)` taken as `(X:[]int)`,
    `<decides>` or `<suspends>` dropped; the Book's tests
    `CoercedOverrides.versetest`): an override has the signature of what it
    overrides, but for a result of a class below the declared one.

## Attributes

An attribute is `@` and a name (Book of Verse ch. 12, "Annotations and
Metadata"; the rules and their sources are pinned in
[research/attributes.md](research/attributes.md)): `@deprecated`,
`@available{MinUploadedAtFNVersion := 3000}`, `@gameplay_element{Category :=
"Combat"}`, `@test("x")`. A space, a new line or another attribute follows
it (`@doc; X:int=4` and `X:int=@doc()4` are syntax errors). It is written
before a definition of a module or of the top level (on its line, or on
lines of its own at the definition's column), a class's or an interface's
field or method, a struct's field or an enum's value; not on a parameter.

```verse
@attribscope_function
perf := class<computes>(attribute):
    MaxMs:int

@deprecated{Message := "Use NewAPI instead."}
OldAPI():int = 42

entity := class:
    @perf{MaxMs := 16}
    Update():void = {}
```

- **The Book's attributes.** `@deprecated` (fields `Message`, a string or
  `false`, and `DiscontinuedAtFNVersion`, an int, which needs a `Message`
  that is not empty), `@experimental` (not on an override) and `@available`
  (field `MinUploadedAtFNVersion`, an int literal) go on functions, methods,
  classes, interfaces, structs, enums and their values, data, modules and
  type aliases; `@attribscope_class`, `_attribclass`, `_enum`,
  `_enumerator`, `_interface`, `_function`, `_data` and `_name` on an
  attribute class. A field the attribute has not, or one given twice, is
  refused, and so is `@deprecated(…)`.
- **Custom attributes.** A class below `attribute` is an attribute class;
  `@c` is its value `c{}`, `@c{F := e}` a value of it, `@f(…)` a call of a
  constructor function of it, each written where one of the scopes on the
  class allows (`@attribscope_function` functions and methods,
  `@attribscope_data` data members, `@attribscope_class` classes, attribute
  classes included, …). Its value is checked as a value of the class, in
  the scope around the definition, which sees no class's member, and is
  never computed. A name that is no attribute class nor a constructor of
  one is no attribute (`@int`, `@c` of a plain class). An attribute class
  and its constructors are named in attributes only.
- **On an expression**, only `@ignore_unreachable` is allowed
  (`F(@ignore_unreachable return)`): it is the expression, and the code it
  makes unreachable is no [warning](#warnings). On a `case` arm it lets the
  arm be one never reached (`@ignore_unreachable E.A => 9` after another
  `E.A`, or a `_` after every value of a closed enum), which then never
  runs.
- **Meaning.** Attributes are metadata: a program cannot read them (ch. 12:
  "there is no Verse API to query attributes at runtime"), and none changes
  what a program computes, but `@available`: openverse's programs are in no
  versioned package, so a definition `@available{MinUploadedAtFNVersion :=
  N}` is in them unless `N` is `4294967295` or more, which no upload
  reaches, and then it and a module's members are taken out (a use of it
  is an unknown name). `@experimental` definitions may be used, as in a
  package that allows them. A use of a `@deprecated` definition (or of a
  member of a deprecated module or enum) from code that is not deprecated,
  and an override of a deprecated member that is not, is a
  [warning](#warnings), `X is deprecated: Message` (the Book's 2009).

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
    `first:` with the clauses indented, then `do:` and a body or nothing;
    generators, `X : Xs`, `I -> X : Xs` and `X := a..b`, as `for`'s, over
    an array, a string or a map (`V : M` its values, `K -> V : M` its keys
    and values, in the map's order) and a range: the
    first iteration whose clauses succeed gives the body's value, what the
    failed ones did is undone, and none fails `first` (ch. 7, "first"; the
    Book's tests, `first.versetest`; [the rules](research/book-forms-rules.md#generators-in-first-and-a-ranges-typed-binding));
    with a generator, each filter must be able to fail, as a `for`'s
    (`first.versetest:28`, "same as `for`"; [the
    rule](research/book-remaining-rules.md#every-filter-of-a-for-can-fail)),
    and commas are refused between the
    clauses of `first{…}`, which join a tuple there, a generator inside it
    not supported yet (`first.versetest:206`).
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
    itself, or binds the name anywhere, a local or a parameter (`Args` is
    openverse's, not the Book's: its tests bind it, `Args:tuple(int, int) =
    (1, 2)`, `DefaultNamed.versetest:274`).
  - With `do EXPR`, `EXPR` runs instead of `Main`, in the context of the
    file's definitions, and its value is printed when it is an `int`, `char`
    or `string`. The expression may fail, which gives exit code 1.
  - A `#!` first line is a `#` comment.

## Warnings

The Book of Verse's compiler gives some diagnostics as warnings: the
program compiles and runs all the same (`FlowControl/Reachability.versetest:22`,
"Treat unreachable expressions after break as warning not error"; its tests
name them with codes 2000–2999 in `assert_semantic_error`). openverse gives
five of them, and one of its own, each from where the fact is known, on standard error as
`FILE:LINE:COL: warning: …`, with the exit status unchanged
([FORMAT.md](FORMAT.md), "Exit protocol"):

- **Code never reached** (the Book's 2000), found in the source
  (`Front/Reachability.lean`). An expression *never completes* when it
  always leaves by a `return` or a `break`: a `return` or `break`; a block
  one of whose statements never completes; an operation (a call, an
  operator, a tuple, array, map or option, a definition, a `set`, a
  `return` of a value) one of whose operands never completes; an `if`
  with an `else` whose branches both never complete; a `case` whose arms
  never complete; a
  `loop` that a `return` leaves and no `break` does; a `sync` one of
  whose arms never completes, a `race` or `rush` all of whose arms never
  complete (`Reachability.versetest` 98-108). The code that comes after
  such an expression, the next statement or the operation that would take
  its value, is never reached, and is reported where it starts, once for
  the code it begins. No `return` or `break` is in a failure context (an
  `if`'s conditions, a `for`'s clauses, …: [Supported](#supported)), so
  such conditions always complete or fail. A `for` whose body returns, a `race` with one
  arm that does, and a `loop` that nothing leaves (in a `<suspends>`
  function, until its task is canceled: `Break.versetest:20` takes the
  code after one with no warning) make no warning.
- **A `return` of a value in a function whose result is `void`** (2002,
  `Return.versetest:179`): the value is discarded. `return F()` of a `void`
  `F` gives none, nor does a body whose last value is not `void` (`F():void
  = 3`, `Return.versetest:178`).
- **A `_` arm after arms that name every value of a closed enum** (2302,
  `Enum.versetest:356`, `Case.versetest:154`): it is never reached. An arm
  after `_`, or with an earlier arm's pattern, stays an error (3616).
- **A use of a `@deprecated` definition** (2009) from code that is not
  deprecated itself, and an override of a deprecated member that is not
  ([Attributes](#attributes), `Attributes.deprecations`): `X is
  deprecated: Message`.
- **`(q:)M(…)` of `Self` in an override of `M`, where `(super:)M(…)` is
  meant** (2003 and 2004, `Bugs/SOL-3564-CallingSuperClassMethodFromOverriddenMethod.versetest`):
  the call is of the slot the override implements, so it dispatches on
  `Self`'s class and calls the override again. 2003 when `q` is what
  `(super:)M` reaches (the implementation above, or the slot's interface
  when nothing above implements it), 2004 when `q` is further up. A call
  of another overload of `M`, one from a method that overrides nothing,
  and one through another receiver give none (`warnQualifiedSelfCall`,
  where a method call is elaborated).
- **A cast that always fails**, `T[X]` where no class of `X`'s type is
  below `T` (openverse's own: the Book's tests accept such casts with no
  code, `Interface.versetest` 140, 150; [Classes](#classes), "Casts").

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
usual failure, binding and rollback behavior. `first` is a reserved name, so
no program defines a function of it.

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
    and the next one starts from the state the choice was reached in. (No
    `return` or `break` can be among the clauses: they are a failure
    context, [Control](#supported).)
  - In a `for`, a choice is one more choice point of the search that the
    `for`'s clauses are (the Book of Verse's rule for a `for`,
    `FlowControl/for.versetest` 317-392; [Readings](#readings-openverse-takes)):
    an alternative none of whose values reaches the body is rolled back, as
    in an `if`, and the next one starts from the state the last body left,
    or, if none did, from the state the choice was reached in; each value
    runs the body, whose effects stay. A choice whose alternatives are
    values (`X := (set N += 1; 1) | 2`, also inside an expression, a
    parenthesized one spliced in) is such a choice point. A `for` whose
    clauses have a call of a function with several values, a choice whose
    alternatives have choices of their own, or an `if`, `case` or `or` that
    picks a branch with a choice keeps, for now, the old rule, entirely: an
    alternative whose own clauses (up to the next generator) fail is rolled
    back; one whose clauses succeed keeps their effects, even when the
    generators after it give no value. The places below that say what stays
    in a `for` are that rule's.

  ```verse
  var N:int = 0
  if (X := (set N = 1; 1) | (set N = 2; 2), X > 1) then Print("{X} {N}")   # 2 2
  var T:int = 0
  for (X := (set T += 1; 1) | 2, Y := 2..X) { Print("{X} {Y} {T}") }       # 2 2 0
  ```
- **Type.** The written type (`X:int = 1 | 2`), or the type of the
  variable or path that `set` writes, else the join of the alternatives'
  types, as for `if`'s branches.
- **`set L = a | b`** evaluates as `set` does: the indices of `L`'s path
  first, then the choice, so each alternative only runs the assignment (for
  `op=`, reading the old value as that alternative finds it). An alternative may have several values or
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
  - `set L op= R` evaluates `L`'s indices, then `R`'s lifted code, then for
    `op=` its old value, as `set` does. A choice or a call with several values
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

  So may a `case` whose arms have them (#283): it is the `if` chain that
  picks its arm, `K := case (e) { p₀ => 0, … }` (its scrutinee once, first,
  its patterns as written, so it fails, or is refused as not exhaustive, as
  the `case` would), then `if (K = 0) then a₀ else if …`, with no choice of
  its own; the picked arm's values are the `case`'s:

  ```verse
  for (X := 1..3, V := (case (X) { 1 => 10 | 11, 2 => Two(20), _ => 5 })) { … }   # 10, 11; 20, 21; 5
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
  operands and nested or lazy consumers. (No `return` can be in a `for`'s
  clauses, a failure context, [Control](#supported).) Breaks inside the body's
  own `loop`s retain their targets. The body may itself consume a lazy choice
  with `for`, a first-success condition or an `option`, including generic and
  mutually recursive producers. These keep their own rollback boundaries;
  ordinary body cleanup also runs when that iteration finishes.
  Refining consumers retain the restrictions of their source scope, including in
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

  An `and`, and the right of `or`, are lifted as blocks are (#283): `A and
  B` as the block of `A` then `B`, a scope of its own whose names `B` sees,
  as without a choice (see [Supported](#supported), Operators). `A and B` is
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

  A range in a block stays an error wherever the block is lifted to, a
  branch included (#283): a range is only a `for`'s iterated expression (the
  Book's rule), so a block's `Y := 1..3` is no generator of the `for` its
  clauses are lifted into. A choice anywhere outside these failure contexts
  is refused: there nothing takes its values, but in the body of a function
  that then has several values (below). (A field reached
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
  a built-in type (`Length`, an array's methods, `ReplaceFirstElement` too,
  a scalar's, `ToChar`, `IsFinite`, …, and `Await`, `Signal`, `Cancel`:
  `builtinMemberNames`), no top-level name and no parameter or local. An
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

  ```verse
  dice := class:
      Sides : int
      Roll()<transacts>:int = 1 | Sides
  Main()<transacts>:void =
      D := dice{Sides := 6}
      for (X := D.Roll(), Y := D.Roll()) { Print("{X}{Y}") }   # 11 16 61 66
  ```

  The function itself is still checked as any function is (types, effects,
  `<decides>`), with each choice read as any of its alternatives.

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

  A block (`block:`) and a `case`'s arm are scopes a `return` leaves the
  invocation from too, as an `if`'s branch is (#283): the rest of the body
  is skipped for each value of the return, and runs, after the scope, for
  the paths that fall through it. A `case` with one picks its arm as it
  would, its scrutinee once, then that arm runs as an `if`'s branch does,
  so its choices are the arm's own:

  ```verse
  F(X:int)<transacts>:int =
      case (X):
          1 => return 10 | 11
          2 => Print("two")
          _ => {}
      X | X + 1
  # F(1): 10, 11; F(2): two, then 2, 3
  ```

  A `return` elsewhere is refused: in a `for` or a `loop` (find what the loop
  looks for first, in a `var` it sets or a `for`'s array, and return in an
  `if` after it), or inside an expression or a condition (`X := if (C) then
  (return 0) else 1`).

  Cleanup stays with the scope that registered it. A returning branch runs
  only the `defer:` blocks it reached, from the innermost scope outward and
  last registered first, after saving each return value. A branch that falls
  through runs its cleanup before the rest of the function. A `defer:` after
  an earlier return path therefore runs only on paths that reach it (code
  follows it in its block, as for any `defer:`, [defer](#defer)).

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
  in a `for` (the old rule, which a `for` taking such a call keeps for now)
  it stays once the second is reached, even if the filter then rejects every
  value after it, and where the first success is taken it is
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
  comparison's later operand (`5 > T[N - 1]`), a `set`'s value, before its
  old value is read (`set K += T(N - 1)`, also as one alternative of a choice
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
  fail it has no values and, in a `for` (by the old rule, which such a `for`
  keeps for now), what came before the call stays.
  Its `defer:` runs as each of its values leaves it, as where it is inlined.
  A generic one may be called at several instances of its type parameters
  in one search (#283): it is taken at each as a callee of its own (one at
  each instance where the first call's does not fit), so the values are
  those of the call at its arguments' types, as anywhere. A generic group's
  own functions are taken at one instance for a whole search: a call of one
  at another, or of a callee recursive with them, is refused.

  ```verse
  Two(N:int)<transacts>:int = N | N + 5
  Digits(N:int)<transacts>:int =
      if (N <= 0) then 0 else Digits(N - 1) * 10 + Two(N)
  Pair(X:t, Y:t where t:type)<transacts>:t = X | Y
  T(N:int)<transacts>:int =
      if (N <= 0) then 0 else:
          S := Pair("a", "bb")
          T(N - 1) + Pair(N, 10) + S.Length
  Main()<transacts>:void =
      for (V := Digits(2)) { Print("v {V}") }   # v 12, v 17, v 62, v 67
      for (V := T(1)) { Print("v {V}") }        # v 2, v 11, v 3, v 12
  ```

  A returning branch may contain plain clauses and
  nested conditionals before its value. A `return` at the end of the body, or
  in an `if`'s branch, a block or a `case`'s arm, ends that invocation, yielding its operand's values in order;
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

  A recursive one's own `defer:`s, and those of a block in its code whose
  values are its own, run as each value leaves their scope (#283), as where
  the function or the block is inlined: after the value is computed and
  before the code after the call (its return frame), last registered first,
  and at a `return` after the return's value. A call whose clauses fail gives
  no value and runs none. In a `for`, what a `defer:` does is part of the
  value's code, undone with it when a filter after the call rejects it:

  ```verse
  R(N:int)<transacts>:int =
      defer: Print("r {N}")
      if (N <= 0) then (0 | 1) else (N | R(N - 1))
  Main()<transacts>:void =
      for (X := R(1)) { Print("v {X}") }   # r 1, v 1, r 0, r 1, v 0, r 0, r 1, v 1
  ```

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
    iterations, and stay, by the old rule, which a `for` taking such a call
    keeps for now (by the Book's rule they would be undone with the call's
    values when none of them reaches the body); what a value does is undone
    with its iteration when the filter rejects it, the return frames it went
    through included (#283);
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

  No `return` or `break` can be in first-success clauses, a failure
  context ([Control](#supported)). Shared helpers retain generic result
  types and witnesses even when only the return type mentions a parameter.

  Refused for now: a recursive one that is not of the generator shape
  above (return frames and choice points in sequence included) and is not
  `<computes>`, keeps local state, or may print or call `Err()`. Its choice
  points must be where a choice is lifted from (a comparison's later
  operand, a `set`'s value, a named argument, a struct's field, `and`'s
  operands, an `if`'s branch, the right of `or`) (#283). Also one with a `return`
  in a `for` or a `loop`, or inside an expression or a condition, or more
  than 16 `if`s with a `return` (the inlined code doubles with each), a method of a class or
  interface below two others that each declare its name without `<override>`,
  one used as a function value, and, since its body is inlined where other names may be
  in scope, one whose name is also the name of a parameter, local, field or
  method anywhere in the program, and a call of one where a name its body
  uses from outside is a parameter, local or member of `Self` in scope.
  Where a lazily taken one's search takes a generic function at one
  instance of its type parameters (above), a call of it at another is
  refused when the function is one of the group's own, is recursive with
  the function whose code calls it or with another, or is overloaded. A
  failure context in a recursive one's code that takes a call's values and
  gives a value of one of its type parameters that none of the names it
  uses has is refused. A call in the clauses copied for each alternative of
  a choice whose values are of different types that would take one overload
  (or one list of an overloaded method) with several values in one copy and
  another in another is refused, saying to write those clauses apart for
  the alternatives or to give the overloads names of their own.
  `Main` never has several values, nor does a `<suspends>` function: a call
  of one with several would have to be in a failure context, and a failure
  context cannot suspend (#156); a choice in its body outside a failure
  context is refused, saying so.
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
types with nothing in common, one of them not comparable, join at `any`:
`if (C?) then 42 else c{}` for a class `c` that is not `<unique>`, and so
does a name bound by the first success of the clauses after a choice whose
values are of such types, after them ([Choice](#choice), #283). Two
comparable types join at `comparable` instead ([comparable](#comparable)):
`if (C?) then 42 else "text"`, `array{15.61, "Message", 3}` (a
`[]comparable`); a map literal's values alike, with no value type
expected (`map{0 => "0", 1 => 1.0}` is an `[int]comparable`, `map{0 =>
c{}, 1 => 1}` an `[int]any`: the Book's tests, `Any.versetest` 131-134).
A `for` whose values are not of the element type expected has its body at
that type, as a typed binding has (`X:[]?int = for (I := 0..2) { false }`
holds three empty options; the Book's tests,
`SOL-4137-MemoryLeakCreatingA3dArray.versetest`). Classes with two common
supertypes are still an ambiguity, and an expected type still decides
(`X:int = if (C?) then 1 else "a"` is refused).

The order of the branches doesn't matter (#366), up to three levels of
such `if`s nested without an expected type (the depth to which a branch is
elaborated against another's, so nesting stays linear): a later branch is
elaborated against the first's type, and when that gives `any` or
`comparable` by having nothing else in common, or the first has no type on
its own, every branch is tried against a later one's
type. So `if (C?) then false else option{4}` is a `?int`, as
`if (C?) then option{4} else false` is, and so is the choice
`false | option{4}`; `if (C?) then array{} else array{4}` is a `[]int`.
Whatever the condition: an index, a `<decides>` call or a cast among its
clauses, first, later or alone, takes it as any (`if (X := Xs[1], X > 1)
then array{X} else array{}` is a `[]int`), and a cast that refines type
arguments types the branch under its refinement (#243, #583).

Nothing can be done with an `any`: it has no equality (so it is no map
key), no `ToString`, and no cast back. So in Verse Core it is `void`: a
value becomes an `any` by being evaluated. In a program that calls
[`ToDiagnostic`](#todiagnostic), which prints any value, an `any` keeps
what it needs to print itself instead: everything above holds of it as
written, with the exceptions listed there.

### ToDiagnostic

`ToDiagnostic(Value:any)<reads>:diagnostic` (the Book of Verse's API
reference: "Accepts any value at all"; ch. 2, "ToDiagnostic()") gives a
`diagnostic`, a class whose `String` is the value's text (the Book makes
the field `<epic_internal>`; its tests read it, and so may a program). An
object of a class that implements `diagnosable`
(`GetDiagnostic()<reads>:diagnostic`) gives its own; a `diagnostic`
implements it by giving itself. The format is the Book's tests'
(`Tests/Intrinsics/ToDiagnostic.versetest`; ch. 2: "The exact format it
produces may vary between VM implementations"):

| Value | Text |
|---|---|
| `false`, `true` | `false`, `true` |
| an int | decimal, `-1000` |
| a rational | reduced, `1/2`, `-1/5`; an integral one as its int, `2` |
| a char | printable ASCII in quotes, `'a'`; a tab, a new line, a carriage return and `" # & ' < > \ { } ~` escaped, `'\t'`, `'\#'`; any other as `0oXX`, `0o7f` |
| a char32 | `0uX` in lowercase hex, `0u1f600` |
| a string | in double quotes, escaped as a char is; a valid UTF-8 sequence of more than one byte `{0uX}`, a byte of none, or another control character, `{0oXX}`: `"Smiley: {0u1f600}"`, `"{0o08}\t"` |
| an option | `option{X}`, an empty one `false` |
| an array | of one element `array{X}`, of any other number `(X, Y, Z)` (none: `()`) |
| a tuple | `(X, Y)` |
| a map | `map{K => V, …}` in its order |
| an enum's value | `e.A` |
| a struct or an object | its type's name (without type arguments) and its fields in declaration order, `my_class{X := 10}`, the object's own class, not its static type's |
| a function | its name and parameter types, `Scale(:int, :float)`; a method's `(c:)M(:int)`; the language's own `(/Verse.org/Verse:)ToDiagnostic(:any)` |
| `()`, a `void` | `false` |

A definition in a module is qualified by it, `(M:)c{…}`; one at the top
level has no qualifier, as openverse's top level has no path (the Book's
tests print the test runner's, `(/Verse.org/VerseTests:)my_class{X :=
10}`). Not pinned by the Book: an empty array, a `void`, a module's
qualifier, a method's.

In such a program, a value of type `t` converted to `any` (as an argument,
a result, a joined branch, an element of a `[]any`, any of the conversions
above) becomes an object of a class the front end writes for `t`, which
prints it when `ToDiagnostic` runs (so an object's `var` fields are
printed as they are then). What a program can do with an `any` is
unchanged; what differs: such a conversion allocates an object, and the
conversion of a value that cannot be printed yet is refused there: a float
(the shortest decimal that reads back, the Book's `1.5`, `1e+100`, needs a
primitive Verse Core does not have yet), a value holding one, a
`comparable` (its box's type is read by no Verse code), a value of a type
parameter (in generic code), a weak map, a type as a value. A program that
never calls `ToDiagnostic`, or that defines `ToDiagnostic`, `diagnostic` or
`diagnosable` itself, is compiled as before.

## comparable

`comparable` is the type of every value of a comparable type (Book of
Verse ch. 11, "Comparable and Equality"): below `any`, above `int`,
`float`, `rational`, `logic`, `char`, `char32`, `string`, enums, structs,
`<unique>` classes, and arrays, options, tuples and maps of such. A value
of one converts to it where a `comparable` is expected (a parameter, a
result, a field, a `var`, an element of a `[]comparable`, a key of a
`[comparable]v`) and by `comparable(X)`; nothing converts back, and a
`comparable` has `=` and `<>` only (no ordering, no `ToString`, no cast; it
is not `<persistable>`). `=` with a `comparable` on either side holds
exactly when both values have the same type and are equal ("These boxed
values maintain their equality semantics"):

```verse
letters := enum{A, B}
numbers := enum{One, Two}
Same(X:comparable, Y:comparable)<decides>:void = X = Y
Main():void =
    if (comparable(15) = comparable(15), comparable("Hello") = "Hello") then Print("equal")
    if (not Same[0, 0.0], not Same[letters.A, numbers.One], not Same[0u41, 65]) then Print("types differ")
    if (Same[(1, 2), array{1, 2}], Same[4 / 2 or 0, 2]) then Print("one value")
    M:[comparable]string = map{0 => "int", 0.0 => "float", letters.A => "A"}
    if (V := M[0.0]) then Print(V)
```

- **Boxes.** A value becomes a `comparable` boxed
  (`OpenVerse/Core/Comparable.lean`, `Code.box`): an enum's value, a
  `char32`, a struct (its fields boxed), a rational that is not an int and a
  map that is not empty carry a code, an int per type, where Verse Core
  holds them like another type's (an enum's value and a `char32` as an
  `int`, a struct as the tuple of its fields); a tuple becomes the array of
  its elements' boxes and an integral rational its int, as Verse has them
  one value; arrays and options are boxed elementwise. An `int`, a `float`,
  a `logic`, a `char`, a string, a `<unique>` object, and arrays and options
  of those, are their own boxes: an `[]int` is a `[]comparable` as it is.
  Verse Core's equality (`Value.veq`) on boxes is then Verse's: the empty
  values of every type are one value, an enum's value is never another
  enum's or an int, one struct at two instances compares field by field.
  In Verse Core a `comparable` is a `dyn`, the type of every value. An
  empty `array{}` or `map{}` where a `comparable` is expected, which says
  nothing of its elements, is the empty value, its own box (`X:comparable
  = array{}`; two of them are equal, as `array{} = array{}` is, Book of
  Verse tests, `Array.versetest:88`).
- **Joins.** Two comparable types with nothing else in common join at
  `comparable` (ch. 1: `array{1, "two", 3.0}`'s element type is
  `comparable`, "their common supertype"; ch. 14: the result "widens all
  the way to `comparable`"), also inside containers (`map{0 => 1} or
  map{1 => 2.0}` is a `[int]comparable`) and beside a `comparable`
  (`array{1} + CA` with `CA:[]comparable`). One that is not comparable
  makes the join `any`.
- **Overloads.** `comparable` overlaps every comparable type and `<unique>`
  classes and interfaces (`F(:int)` and `F(:comparable)` cannot both be
  defined), and is distinct from the types that are not comparable.
- **Generic code.** A type parameter declared `subtype(comparable)` whose
  value a generic function compares with a value of another type, or passes
  or binds as a `comparable`, takes the box of its instance as the evidence
  of that bound ([Parametric functions](#parametric-functions)):
  `Equal(X:t, Y:comparable where t:subtype(comparable))<decides>:t = X = Y`,
  `Same(X:t, Y:u …) = X = Y` and a `tuple(t, t, t)` against a `string`
  compare by value and type.
- Not yet: a value of a type parameter as a `comparable` other than as an
  argument, a result, a local's value or an operand of `=` and `<>` (an
  element of an array literal, a map key, a field); a struct at type
  parameters converted to `comparable` (`X:comparable = P`, `P:p(t)`); and
  `case` on a `comparable`.

## Weak maps

`weak_map(k, v)` (Book of Verse ch. 3, "Weak Maps"; the rules, the tests and
the design are in [research/weak-map.md](research/weak-map.md)) is a
supertype of `[k]v` that keeps only entry access: "It behaves similarly to
ordinary maps for individual entry access, but deliberately restricts bulk
operations."

```verse
base_class := class<unique> {}
derived_class := class(base_class) {}
Main()<decides>:void =
    var W:weak_map(int, int) = map{}
    set W[0] = 1                        # insert or update, in a failure context
    W[0] = 1                            # fails when the key is absent
    set W = map{0 => 2}                 # a local is replaced whole
    if (set W[5] = 5, false?) {}        # undone with the failure context
    not W[5]
    K := derived_class{}
    M:[derived_class]int = map{K => 3}
    B:weak_map(base_class, int) = M     # a map is one, and keys are covariant
    B[K] = 3
```

- **The type.** `k` must be comparable, and holds no array or map but `string`, as a map's key (a weak map is "a map that does not keep its keys alive", ch. 3: [the rule](research/book-remaining-rules.md#map-keys-and-a-refinements-range)). A `[k]v` converts to a
  `weak_map(k', v')` and a `weak_map(k, v)` to a `weak_map(k', v')` when `k`
  is below `k'` and `v` below `v'` (ch. 3, "Covariance"); nothing converts a
  weak map to a map or to `comparable`, and a weak map has no `=`. A weak map
  and a map join at a weak map (`if (c) then W else map{…}`), and a function
  of a `[int]int` and one of a `weak_map(int, int)` join at a function of a
  `[int]int`. It may be a local, a parameter, a result, a field of a class
  or a struct (not a `<persistable>` one's: it does not persist, ch. 17), an
  element of a container and a type argument.
- **Entries** are a map's: `W[k]`, `set W[k] = v` (in a failure context, as
  a map's), `set W[k] op= v`, and paths through an entry, `set W[k].F = v`,
  `set W[k][i] = v`, with their rollback. A key of a class above or beside
  the map's key class reads (`W[K]` with `K` of a class above the keys': it
  is looked up at the class above both, as the API's
  `operator'()'(Map:weak_map(t, u), Key:t)` takes it; a map's too); a write
  needs a key of the map's key type.
- **Refused**: `W.Length`, `for (X : W)`, `ConcatenateMaps` of one, `=` and
  `<>`, `comparable(W)`, a weak map where a map is expected, and a weak map
  as a map's key; each with the Book's words ("There is no `Length`
  property, no iteration, no coercion to `comparable`"). There is no
  removal: a map's entries are removed by iterating it, which a weak map
  cannot be.
- **Weak keys.** No program can tell whether an entry whose key is no
  longer referenced is still there: a weak map is read only by `W[K]`, with
  a key equal to the entry's, and a key that holds an object is equal only
  to one holding the same object, which a program that holds it keeps
  alive. openverse never reclaims objects, and holds a weak map as a map,
  the array of its pairs in Verse Core; the argument is
  [research/weak-map.md](research/weak-map.md), "Is weakness observable?".
- Not yet: `weak_map(…)` as a value (`t := weak_map(int, int)` in a body),
  as types as values are classes' and interfaces' only.

## Module-scoped variables

A `var` at the top level or in a module is a variable of the program (Book
of Verse ch. 3, "Module-Scoped weak_map Variables"; ch. 16, "Module-Scoped
Variables"; ch. 18, "Persistent Variables";
[research/weak-map.md](research/weak-map.md)), and it is only ever a
`weak_map`, read and written one entry at a time:

```verse
key := class<unique><persistent><module_scoped_var_weak_map_key>:
    Id:int
saved := struct<persistable>:
    Level:int = 1
progress := module:
    var Levels<public>:weak_map(key, saved) = map{}
    GetLevel<public>(K:key)<transacts>:int =
        if (S := Levels[K]) then S.Level else 1
    SetLevel<public>(K:key, L:int)<transacts><decides>:void =
        set Levels[K] = saved{Level := L}
```

- **The rules**, each refused otherwise, as the Book's tests refuse them
  (3502): its type is a `weak_map` ("Direct `var` declarations of simple
  types (like `var X:int = 0`) are not allowed at module scope"); its key
  type a class with `<module_scoped_var_weak_map_key>`; when that class is
  `<persistent>`, its value type persists (ch. 17, as a `<persistable>`
  struct's fields must: not `rational`, `any`, `comparable`, a class, a
  weak map, or a struct or an enum that is not `<persistable>`); `X[k]`, `set X[k] = v` and paths through `X[k]` are its uses,
  and any other use of `X`, reading or replacing the whole map, is refused
  ("The complete map can neither be read nor replaced"); at most four with
  `<persistent>` keys, and at that limit one of them with a class value
  (the tests' "Set to 4 for VerseTestScriptCmd", `weak_map.versetest`
  623-664). `<persistent>` and `<module_scoped_var_weak_map_key>` are class
  specifiers.
- **Uses.** An entry is read with `<reads>` and written with `<writes>`
  (`<transacts>` has both), from any function, method, `<suspends>`
  function or task, and a failure context undoes the writes in it. A local,
  parameter or member named like one is refused, as for a constant. Its
  name's access is the module's (`<public>` to be used outside it).
- **Its value** starts as `map{}` before `Main` runs and lives until the
  program ends: the `var` fields of one object made by `Main`'s prelude
  (`$module_state`, [DESIGN.md](DESIGN.md#weak-maps-and-module-scoped-vars)).
- Not yet: an initial value with entries (every module-scoped `var` of the
  Book starts as `map{}`), and so a declaration with none, `var X:t` on its
  line (valid syntax, the Book's tests, `Pointers.versetest:4`; refused, as
  openverse has no variables defined elsewhere); `var<w>` write access on one; the engine's key
  types (`player`, `session`, `persistent_key`, `session_key`), and
  persistence itself: openverse runs one program, whose module state starts
  empty.

## Types as values

A class or an interface is a value of a *metatype* (Book of Verse ch. 11,
"Metatypes"; the forms, what is built and what is left are in
[research/types-as-values.md](research/types-as-values.md)):

```verse
shape := class<abstract>:
    Area():int
square := class<concrete>(shape):
    Area<override>():int = 4
circle := class<concrete>(shape):
    Area<override>():int = 3

Make(T:concrete_subtype(shape)):shape = T{}        # constructed through T
Is(T:subtype(shape), S:shape):int =
    if (T[S]) then 1 else 0                         # cast through T
Main():void =
    Kind:subtype(shape) = square                    # a class as a value
    Print("{Make(circle).Area()} {Is(Kind, square{})} {Is(Kind, circle{})}")
```

- **`subtype(c)`** holds `c` and the classes and interfaces below it, of a
  class or an interface `c`; `subtype(a)` is below `subtype(b)` exactly
  when `a` is below `b`, and every metatype is below `type`.
  `castable_subtype(c)` holds the `<castable>` ones, `concrete_subtype(c)`
  the `<concrete>` ones. A join of two type values (`if (B) then square else
  circle`) is at the nearest metatype above both, never a
  `concrete_subtype` and a `castable_subtype` only of a `<castable>` class.
- **`T[X]`** with `T` a type value is `X` cast to the class `T` holds, failing
  unless `X`'s class is below it. **`T{}`** with `T:concrete_subtype(c)`, a
  local or, in a method, a field of the class (ch. 11: "The type value has
  to be held in a class *field*"), constructs the class `T` holds with its
  defaults; no field may be given.
  Naming a type as a value, and casting through one, has no effect, so a
  `<computes>` function may do both; `T{}` has the construction effects of
  every `<concrete>` class at or below `c`, any of which it may construct
  (the Book's tests, `SOL-8627-concrete_subtype-effects`).
- **Other types.** `subtype(t)` is also of a type that is no class or
  interface: a built-in type (`subtype(int)`), a struct, an enum, or an
  array, option, map or tuple of them (`subtype([]c)`); its values are the
  types `t` (`X:type = int`, `Identity(point)`), each an object of a class
  of its own, which nothing reads but a conversion to `type`, and a value
  of `subtype(t)` holds `t` alone. `castable_subtype` and `concrete_subtype`
  of such a type are refused, as the Book's tests have them. `any` and
  `comparable` are values of `type` too (`X:type = any`), with no
  `subtype(any)` or `subtype(comparable)`.
- **`concrete_subtype(any)`** holds the `<concrete>` classes, and
  **`concrete_subtype(comparable)`** those that are also `<unique>`, so
  comparable (`concrete_subtype(comparable)` of `float` is refused); nothing
  is constructed through them (the Book's tests: "comparable cannot be
  instanced here because we don't know if it's a class type").
- Type values are not compared (the Book's tests: "We can't yet compare
  the subtype values"). `subtype(any)`, `subtype(comparable)`,
  `castable_subtype(any)`, `subtype(t)` of a type parameter and
  `concrete_subtype(c)` as a type parameter's bound are not supported;
  `subtype(c)` and `castable_subtype(c)` as a type parameter's bound are
  ([Parametric functions](#parametric-functions), "Upper bounds").
- **A type given as an argument.** A function's parameter `t:type` that the
  function uses as a type (`FalseOption(t:type):?t = false`, the Book's
  tests) is a type parameter whose argument the call writes:
  `FalseOption(int)`, `Pair(int, 1, 2)` with `Pair(t:type, X:t, Y:t)`, and
  in brackets for a `<decides>` function, `First[string, Xs]` with
  `First(t:type, Xs:[]t)<decides>:t`. The
  function is generic over `t`, so checked once, and the call passes the
  type's witness, as a generic call does. A parameter `t:subtype(c)` or
  `t:castable_subtype(c)` used so is a bounded one (`where t:subtype(c)`,
  [Parametric functions](#parametric-functions), "Upper bounds"): `Count(t:subtype(shape),
  Xs:[]t)`, called `Count(square, …)`; a type outside the bound is refused,
  as for a bounded type parameter. The argument is a type as written:
  a type's name (`int`, `logic`, a class's, a struct's) or a parametric type
  applied (`c(int)`, `tuple(int, float)`); `[]int` and `?int` are not yet
  written as arguments. Refused: a value there, a type parameter there (the
  BPVM's link error; VerseVM accepts it), such a parameter after a parameter
  whose type uses it (`F(X:t, t:type)`, the Book's tests, 3502), and such a
  parameter of a method.
  A parameter `t:type` used as a value is a type value's (above).
- **Conversions.** `t(X)`, with `t` a built-in type's, a struct's or an
  enum's name, or a type written in parentheses, `(?int)(X)`, `([]int)(X)`,
  is `X` converted to `t`: `X` must have a type that is a subtype of `t`
  (`int(0.0)` is refused; `void(0)` takes anything), as `c(X)` is for a
  class and `comparable(X)` for `comparable`.

## Equality and the empty value

Verse has one empty value, written `false` or `()` (Book of Verse ch. 2,
"void, true, tuple() and false"): it is the `logic` false, the value of
`void` and `tuple()`, the empty option, and the empty array, string and
map. `=` and `<>` compare values (ch. 4: "Comparisons between different
types still compile, but they always fail"), so any two comparable types
may be compared, and two values of different types are equal only when
they are one value: the empty value, a tuple and the array of its
elements (`('a', 'b') = "ab"`), an int and the rational it is, or
containers and one struct's instances of such
(`p(tuple(int, int)){X := (1, 2)} = p([]int){X := array{1, 2}}`):

```verse
Main():void =
    A:[]int = array{}
    O:?int = false
    M:[string]int = map{}
    if (A = false, false = A, O = "", () = M, A = O) then Print("one value")
    if (not 0 = 0.0, not 0u41 = 65, not array{1} = "a") then Print("different types")
```

Verse Core's equality (`Value.veq`, `docs/CLAIMS.md`) is Verse's for the
empty value: structural, but `false`, `()`, the empty option and the empty
array, string and map are one value however Verse Core holds them, at every
depth, so `array{false} = array{()}`, `option{false} = option{()}` and, in
generic code, `X = false` for an empty `X:t` at any `t` hold. Where Verse
Core holds values of different types alike, the front end decides from the
two types (`TyEnv.cmpPlan`, research note
[empty-values.md](research/empty-values.md)): two types with nothing in
common are never equal (a `char32`, an enum and an `int`, two structs of
one layout: `0u41 = 65` fails), and two with only the empty value in common
whose other values Verse Core could find equal are equal exactly when both
are empty (`[]int` and `[]char32`). An operand is converted to the other's
type only where that keeps values apart (a tuple to an array, an int to a
rational, one struct at another instance), never to `void`: `(1, 2) =
array{(), ()}` fails. An empty `array{}` or `map{}` compared with a value of
another type is that type's empty value.

An empty `array{}` or `map{}` with no type from its context (`A := array{}`,
`array{}.Remove[0, 0]`, `Map := map{}`), and `Concatenate()`, are of
`false`, the type with no values: `[]false`, `[false]false`, which convert
to every array or map type, so `A + array{1}` is a `[]int`, `array{} = ""`
compares at `string`, and in `for (X : array{}, Y : array{1}) { X + Y }`
the operand `X` of `+` has the other's type; the Book's tests
(`Array.versetest:90`, `Map.versetest:236`, …; [the
rule](research/book-forms-rules.md#an-empty-container-with-no-type-from-its-context)).

Where neither is decided from the types, both operands are boxed and
compared as `comparable`s ([comparable](#comparable)): two types with
other values in common that Verse Core cannot tell apart
(`[]tuple(int, []int)` and `[]tuple(int, []char32)`, an int beside a
rational inside containers), and, in generic code, a type parameter and
another type, two type parameters, or a tuple of type parameters and a
string, by the box of the instance (the evidence of its
`subtype(comparable)`). So an empty struct is not `()` in generic code
either (`IsFalse(X:t where t:subtype(comparable))<decides>:void = X =
false` fails at `s{}`).

`void` takes any value and makes it the empty value; `tuple()`, which the
Book also writes `true`, is the type of the empty value alone: `false`,
`()` and a `void` value convert to it, it converts to `void`, to an array
and, as the Book's `true` does ("true is a subtype of logic"), to `logic`
as `false`, and `X:true = 1` is refused. A `void` value converts to
`logic` as `false` too (`X:logic = if (C?) then () else true`), and
`void` and `true` interchange inside options, arrays and maps (`?void` to
`?true`, `[]void` to `[]true`, `[int]void` to `[int]true`), as the Book
has them one type (ch. 2: "These are interchangeable"); not yet as a
function type's result or parameter (`int->true` is not `int->void`).
`void` given as a type argument of a program's parametric class,
interface or struct, as a type or a parent (`box(void)`, `box([]void)`,
`class(holder(void))`), is `true`: a type parameter bound to it takes the
empty value alone, so `box(void){}.Put(1)` and `box([]void){}.Put(Y)`
with `Y:[]int` are refused, where `Sink(:[]void)` takes `Y` (ch. 2, "Write
the value, not the type name" and "Conversion is one-way"; the library's
`task(void)` and events keep `void`). A `branch:`'s value is an
`any`, which `void` takes and `true` does not (the Book's tests refuse
`Result:true = branch: …`). `false` converts to an empty option or array but not to a map
(the Book's tests refuse it, `Tests/Map.versetest` 343, though its prose
allows it). As overloads, two types that both hold the empty value are not
distinct (`logic`, options, arrays, strings, maps, `tuple()`); `void` is
distinct from none; `tuple()` is distinct from `int`.

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

## Type aliases

A type alias is a name for a type (Book of Verse ch. 10, "Aliases"; ch. 11,
"Type Aliases"; the rules and their sources are in
[`research/type-aliases.md`](research/type-aliases.md)):

```verse
player_id := int
coordinate := tuple(float, float)
handler := type{_(:float):void}
predicate(t:type) := t -> logic          # a parametric alias
string_map(t:type) := [string]t
shape := class:
    Sides:int = 3
figure := shape

IsEven(X:int):logic = logic{Mod[X, 2] = 0}
Count(P:predicate(int), Xs:[]int):int = (for (X : Xs, P(X)?) { X }).Length
Main():void =
    ID:player_id = 42                       # an int
    Scores:string_map(int) = map{"a" => 1}  # a [string]int
    F := figure{}                           # a shape
    Print("{ID} {F.Sides} {Count(IsEven, array{1, 2, 4})}")   # 42 3 2
```

- **A type or a value.** A definition `name := e` at the top level or in a
  module defines a type alias when `e` is a type: written as only a type
  can be (`?t`, `[]t`, `[k]v`, `tuple(…)`, `t->u`, `type{_(…):r}`,
  `logic`), or the name of a type (a built-in type, a class, interface,
  struct, enum, refinement type, or another alias; also `M.c`), or a
  parametric type's name applied to as many types as it has parameters
  (`box(int)`). Otherwise it would be a constant without its type, which a
  module's scope, the top level's too, does not allow (ch. 16: "All data
  definitions at module scope must also explicitly specify their type";
  the Book's tests, `Union.versetest` 23, 290): `X := Y` with `Y` a
  constant, `X := F` with `F` a function (a built-in too, `X := Sqrt`),
  `X := F(1)`, and `X := c(Y)` and `X := any(Y)`, a cast and a conversion
  of the constant `Y`, are refused; such a constant is written `X:t = e`.
  `name(t:type, …) := e` is always a type: a parametric class, interface,
  struct, or alias. A definition with a written type, `X:t = e`, is never
  an alias. (`X := c` with `c` a class was refused before aliases: `c` was
  no value; it is now an alias of `c`.)
- **The type it names.** An alias is not a new type: it is the type it
  names everywhere, in assignments, overloads (`F(X:player_id)` and
  `F(X:int)` cannot both be defined), casts and comparisons, and messages
  show that type, not the alias. A parametric alias is applied to as many
  type arguments as it has parameters, each `t:type` (a bound,
  `t:subtype(…)`, is not supported).
- **Where a type's name is.** An alias of a class, interface, struct, enum
  or refinement type stands for it where a construction (`figure{}`,
  `(figure){}`), a
  parent (`class(figure)`), a cast (`figure[X]`), a qualifier
  (`(figure:)M()`) or an enum's value (`hue.Red`) names it; a parametric
  one as `box_of(int){…}`. Any other alias is no value: `maybe := ?int`
  makes `maybe{}` and `maybe[X]` errors.
- **Where.** At the top level or in a module, `<public>` to be used outside
  it, as `M.point`; not in a class or a function. A module's alias is no
  data, so it needs no written type.
- **In order.** An alias is used only after its definition (in the order
  the definitions are loaded: an imported file's first), so `b := ?a`
  before `a := int`, or a class with a field of type `a` before it, is an
  error; an alias may name a class or struct defined after it. An alias
  that names itself (`list(t:type) := ?tuple(t, list(t))`) is an error: a
  class can hold a value of its own type. No definition, at any scope,
  takes an alias's name, nor a built-in type's, but a parametric class,
  interface or struct of another number of type parameters, in the same
  scope and in either order: `class1() := class1(int)` beside
  `class1(t:type) := class…`, where `class1()` is the alias and
  `class1(string)` the class (the Book's tests,
  `ParametricTypes.versetest:754-768`, `Bugs/SOL-7503…`, `Bugs/SOL-7849…`).
  Two classes of one name, or an alias at the type's own number, are still
  defined twice.
- **Checks.** The names in an alias's type, and how many type arguments
  each is given, are checked where the alias is defined; the rest (a map
  key or a type argument that must be comparable) where it is used, as if
  the type were written there.
- **Access.** An alias is `<internal>` by default, or `<public>`,
  `<scoped{…}>` or `<epic_internal>` (`<protected>` and `<private>` are
  for a class's members), and is no more visible than what it names: `c :=
  class{}` and `a<public> := c` is an error (Book of Verse ch. 11; see
  [Access](#access)).

## float

A `float` is an IEEE 64-bit float (Book of Verse ch. 2, #127), except that
it has one NaN, which equals itself, and no negative zero:

```verse
Area(R:float):float = 3.14159 * R * R

Main():void =
    Count:int = 5
    Print("{Area(2.0)} {Count * 1.5} {0.1 + 0.2}")   # 12.566360 7.500000 0.300000
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
- `ToString`, and string interpolation, which calls it, give fixed point
  with exactly six digits after the point (the Book's API and
  `FloatToString.versetest`): the float's exact value rounded to a multiple
  of 10^-6, a tie to the even digit (`98.500000`, `1.234568` for
  `1.2345678901234567`, `0.007812` for `0.0078125`), every digit before the
  point (`1.0e100` prints its exact binary value, 101 digits, then
  `.000000`), a `-` whenever the float is negative, also when every digit
  is zero (`-0.000000` for `-1.0e-300`; `-0.0` is `0.0`, which prints
  `0.000000`), and `Inf`, `-Inf`, `NaN`. It is lossy: to show a value's
  bits, print it times a power of two. (Until the Book's rule was adopted,
  openverse printed the shortest decimal that reads back, `98.5`, as ch. 2's
  example does; [the audit](research/readings-audit.md#tostring-of-a-float).)

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

## Bitwise functions

The Book's ch. 4 ("Bitwise Operations", "Bit Shift Operations") and its
API reference: of ints, on their two's complement bit patterns, "sign-extended
forever to the left", on openverse's 64-bit ints (the Blueprint VM's: a
result out of range is the overflow error, exit 2; [the pinned
rules](research/book-library-functions.md#bitwise-functions)):

```verse
Main():void =
    Print("{BitAnd(12, 10)} {BitOr(12, 10)} {BitXor(12, 10)} {BitNot(12)}")   # 8 14 6 -13
    if (L := BitShiftLeft[-5, 2], R := BitShiftRight[-97, 5]) then Print("{L} {R}")   # -20 -4
    if (not BitShiftLeft[5, -1]) then Print("a negative count fails")
```

- `BitAnd(X, Y)`, `BitOr(X, Y)`, `BitXor(X, Y)` and `BitNot(X)` (which is
  `-X - 1`) never fail and are never out of range.
- `BitShiftLeft[X, N]` is `X · 2^N` and `BitShiftRight[X, N]` is
  `Floor(X / 2^N)` (an arithmetic shift: toward minus infinity, so 0 or -1
  once every bit is shifted out, `BitShiftRight[-1, 1000]` is -1); both
  fail when `N < 0`. A left shift out of range is the overflow error
  (`BitShiftLeft[1, 63]`; `BitShiftLeft[-1, 63]` is the least int;
  `BitShiftLeft[0, N]` is 0 for every `N ≥ 0`).
- Each argument is evaluated once, in order; floats are refused. They are
  soft built-ins, as `Clamp` is (a program may define its own), and of one
  signature, so a program may name one as a value (`F(:int, :int):int`,
  the shifts `<decides>`).
- On VerseVM ints are unbounded and so are these; openverse's are not
  (see [Readings](#readings-openverse-takes), `int` range), so the Book's
  `verse_vm_only` cases with operands beyond 64 bits differ.
- They are written in Verse with Verse Core's existing operations
  (`Front/Bitwise.lean`; DESIGN.md, "Bitwise functions"): no Verse Core,
  format or runtime change.

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
  values and paths, in `set`'s order (the right operand, then the old
  value) and with its rollback rules. Int/int and float arithmetic keep their existing behavior.

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
elaborator generates (Core has no conversion from int to char). A `char32`
and an `int`, which Verse Core holds alike, are never equal, as values of
different types ([Equality and the empty value](#equality-and-the-empty-value));
`=` and `<>` between two type parameters, or between one and another type,
compare the instances' boxes ([comparable](#comparable)), so `0u41` and `65`
differ in generic code too. A
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
        Power<public>:int
        Cast<public>():int = Power * Inner.Factor + Base

using{spell}

Main():void =
    Print("{spell.Bonus} {spell.Inner.Scale(2)} {Inner.Scale(3)}")
    W:spell.wand = spell.wand{Power := 2}
    Print("{W.Cast()}")
```

- A module is `name := module:` with its definitions indented, or
  `name := module{…}`. It holds functions, constants, structs, enums,
  classes, interfaces, [type aliases](#type-aliases) and other modules. A
  constant in a module, as at the top level, states its type (`X:int = 1`, not `X := 1`); an
  alias is no constant (`point<public> := tuple(int, int)`). A module is
  not a value. A module may be defined in parts, `M := module:` written
  again in the same scope: the parts are one module, one scope, whose
  members are all the parts'; the parts have one access level and give
  the same `@available`, or none (the Book's tests,
  `PartialModuleDefinitions.versetest` 157-176, `available.versetest`
  317-368; ch. 16: a module's files share its namespace).
- A name is looked up from its definition's module outward, one scope at a
  time, up to the top level. At each scope, the scope's own definitions
  come first, then the members of the modules it opens with `using{M}`.
  If two modules opened at the same scope give the name, it is ambiguous
  and an error. The first definition or module found is the one meant;
  only a qualified definition may have the name of one around it
  ([Shadowing](#shadowing)).
- `(M:)F` and `(A.B:)F` are `M.F` and `A.B.F` (#145): values, functions,
  the type `(M:)c` and the construction `(M:)c{…}` (#147); a member may be
  defined `(M:)F` in `M` (see [Qualified names](#qualified-names)).
- `M.F`, `A.B.F`, the type `M.c`, the value `M.c{…}`, a delegation
  `M.D<constructor>(…)` and a qualifier `X.(M.i:)F()` name a member. `M`
  is looked up like any name; if a value is found instead, `.F` is its
  field. Each level used from outside it must be `<public>` (or admit the
  use otherwise, [Access](#access)), including each module of a
  `using{A.B}`. Members are `<internal>` by default: visible in their
  module and its submodules. A name's overloads have one access level. A
  member a `using` opens that the use may not see does not make a name
  ambiguous.
- An extension method `(R:t).M(…)` of a module is found by calls `X.M(…)`
  as its members' names are, `<public>` from outside
  ([Extension methods](#extension-methods)).
- Verse does not allow shadowing (Book of Verse ch. 10, "Shadowing and
  Qualification"): see [Shadowing](#shadowing). A local, parameter or class
  member (inherited ones included) named like a visible module or module
  member (its own module's, or an open module's) is an error too.

Modules exist only in the front end. Each member becomes a definition of
its qualified name before elaboration, and messages show it as `M.F`.

## Access

An access specifier says from where a definition may be used (Book of Verse
ch. 12; the rules, with their sources in the Book's chapters and tests, are
pinned in [research/access-specifiers.md](research/access-specifiers.md)):

```verse
Store<public> := module:
    inventory<public> := class<internal>:            # constructed only in Store
        var<private> Items<public>:[]string = array{}  # read anywhere, set by inventory
        Capacity<private>:int = 2
        AddItem<public>(Name:string)<transacts><decides>:void =
            Items.Length < Capacity
            set Items += array{Name}
    MakeInventory<public>():inventory = inventory{}
entity := class:
    var Health<protected>:int = 100                 # entity and the classes below it
player := class(entity):
    Hit():int =
        set Health -= 25
        Health

Main():void =
    Bag := Store.MakeInventory()
    if (Bag.AddItem["sword"]) then Print("{Bag.Items.Length}")   # 1
    Print("{player{}.Hit()}")                                      # 75
```

- **What each admits.** A use is written in code at a module (the top level
  is the program's root module) and, in a method, a field's default or a
  `block:`, at a class. `<public>`: any code. `<internal>`, the default:
  code in the definition's module or a module inside it. `<protected>`:
  code of the definition's class or interface, or of one below it, in any
  module. `<private>`: code of the class itself, not of one below it.
  `<scoped{M, N.P}>`: code in the definition's module or in one of the
  modules named, or inside them; an access level may be named, `S :=
  scoped{M, N}` and `<S>` or `<A.S>`, and has an access of its own.
  `<epic_internal>`: Epic's code, which a program is (a reading, below).
- **A path.** A use names a path, and each step must admit it: `A.B.c`
  needs `A`, `B` and `c`. A member reached through a value, `X.F`, is
  admitted where its declaration (the one that introduces it, whose access
  its overrides have) is: its own access, its class's, and its class's
  modules'. Scoping a definition does not scope its members.
- **Where each is written.** A module and a module's definition (function,
  constant, class, interface, struct, enum, type alias): `<public>`,
  `<internal>`, `<scoped>` or `<epic_internal>`. A class's or interface's
  field or method: any. A struct's field: `<public>` only (its fields are
  public). After `class`, its constructor's: not `<private>`; after
  `struct` or `interface`: not `<protected>` nor `<private>`. On `var`, a
  field's write access. One access specifier per place; none on an
  override, which has the access of what it overrides; none on a local or a
  parameter; a function's is written on its name, `F<public>(…)`.
- **Read and write.** `var<w> X<r>:t` is read where `<r>` admits and set
  where both do (`<w>` absent restricts nothing more); `<w>` is at least as
  restrictive as `<r>`, judged with what the field is in. A construction gives a field a value where reading
  admits it.
- **Constructors.** `c<public> := class<internal>{…}` is a type all may
  use and only its module constructs or extends: from outside, a function
  of its module makes one. `class<protected>` is constructed by the classes
  below. A construction `c{F := e}` needs the constructor and each field it
  gives; a class needs its direct parents' constructors.
- **A definition exposes nothing less visible than itself.** The types a
  function's or method's parameters, result and bounds, a constant's or
  field's type, a struct's fields and a type alias name (type arguments
  included) are each at least as visible as the definition, judged with
  what it is in: a `<public>` function in an internal module or class may
  name an internal class; a `<protected>` method of a `<public>` class
  reaches classes below it in any module, so it may not; a `<private>` one
  may. A class's or interface's field with no default is at least as
  visible as the class's constructor, which gives it its value.
- **Readings.** openverse has no packages: a program is one, its top level
  the root module, standing where the Book's test snippets do, in an
  Epic-internal scope, so `<epic_internal>` admits all of the program and
  orders above `<internal>` and `<scoped>`, below `<public>`. A scope names
  modules of the program; a package's path (`scoped{/Verse.org}`) is
  refused. A name's overloads in one module or class have one access.

Access is a compile-time rule: nothing is generated for it. A module's
members are checked where the modules' renaming resolves them; a
construction, a parent and an override on the resolved program; a member
reached through a value where the elaborator finds it (see
[DESIGN.md](DESIGN.md#access-one-order-checked-where-names-are-resolved)).

## Shadowing

No definition takes the name of a definition of a scope around it, whichever
is written first (Book of Verse ch. 10, "Shadowing and Qualification": "you
cannot redefine names that already exist in an enclosing scope"; the rule
is pinned in [research/qualified-names.md](research/qualified-names.md#shadowing)):

```verse
Limit:int = 3
box := class:
    (box:)Limit:int = 10        # Limit:int = 10 would be refused
    Twice():int = 2 * (box:)Limit
Main():void = Print("{Limit} {box{}.Twice()}")   # 3 20
```

- **Scopes.** The top level and the modules nest; a class, an interface, a
  struct or an enum is a scope inside the one it is defined in; a function's
  parameters and locals are inside the function's. A member of a module, a
  module, a field or method of a class or interface, a struct's field, an
  enum's value, a parameter and a local cannot take the name of a definition
  of a scope around it, the type it belongs to included (`c := class:
  c():c` is refused). Sibling scopes do not meet.
- **Functions overload across scopes.** A function or a method may take the
  name of a function around it when no call could fit both (`F()` and a
  method `F(X:int)`), as overloads in one scope may
  ([Overloading](#overloading)); one a call could fit both of is refused. A
  parameter of a function type may take such a name; in the function's body
  the name is the parameter. A function and a definition of another kind
  never share a name.
- **Exempt.** A qualified definition, which says where it is: `(M:)x`,
  `(c:)m`, `(e:)v`, `(local:)X` ([Qualified names](#qualified-names)); its
  bare uses are then ambiguous where the other definition is visible (in a
  class's code and for `(local:)`), or the inner one (in a module). An
  override, which defines no name. The entry point `Main`, which is
  openverse's and not the Book's.
- The message names both definitions and the qualifier to write: "the field
  'Limit' of box has the name of the constant Limit (1:0): Verse does not
  allow shadowing (Book of Verse ch. 10); rename one, or qualify this one,
  (box:)Limit".

## Qualified names

A qualifier `(q:)` names a scope, and a qualified name is looked up in
exactly that scope and nowhere else (Book of Verse ch. 9, 10 and 16; the
rules, their sources and the readings are pinned in
[research/qualified-names.md](research/qualified-names.md)):

```verse
Store := module:
    Factor<public>:int = 7
    (Store:)Twice<public>(X:int):int = 2 * X       # Twice, a member of Store
    Scale<public>((local:)Factor:int):int =         # a parameter named like Store.Factor
        (local:)Factor * (Store:)Factor
counter := class:
    var (counter:)Total<public>:int = 0             # the field Total
    Add<public>():int =
        set (counter:)Total += 1
        (counter:)Total
keyword := enum{(keyword:)for, (keyword:)if}       # values named like keywords

Main():void =
    Print("{(Store:)Twice(3)} {Store.Scale(2)} {counter{}.Add()}")   # 6 14 1
```

- **What a qualifier names.** `(M:)` and `(A.B:)` a module, found as any
  name is, from the use outward; `(c:)` a class, interface, struct or enum
  (or an alias of one); `(local:)` the locals of the code it is written in;
  `(super:)` the implementation above a method ([Classes](#classes)); a path
  `(/Verse.org/Verse:)` openverse's built-in types. Any other path names a
  package or an engine module openverse has no stand-in for, and is refused;
  so is a qualifier that names nothing.
- **Uses.** `(M:)x` is `M`'s member `x` (as `M.x`); `M.(M:)x` too. `(e:)v`
  is the enum's value `e.v`. `(c:)F`, `Self.(c:)F` and `X.(c:)F` are the
  field `F` that `c` declares itself, of an `X` of `c` or a class below it;
  `X.(c:)M(…)` calls the method `M` that `c` *introduces* (a class or
  interface that inherits or overrides `M` is refused: qualify with the one
  that declares it first, as the Book's tests do). `(local:)X` is the local
  `X`, defined `(local:)` or not; `(/Verse.org/Verse:)int` is `int`.
  `X.(M:)F(…)` calls the extension method `F` of the module `M`
  ([Extension methods](#extension-methods)). `using{(A:)B}` is `using{A.B}`. A redundant qualifier is no error.
- **Definitions.** A definition's qualifier names where it is defined:
  `(M:)x` in module `M`; `(c:)m` or `(c:)F:t` in class `c` (a member that
  then is `m` or `F`), and `(r:)M<override>` in a class below `r`, which
  implements the `M` that `r` introduces ([Overloading](#overloading),
  [Classes](#classes)); `(e:)v` in enum `e`, where `v` may be a keyword or a
  reserved word; `(s:)f` in struct `s`; `(local:)X` for a local, a `var`, a
  `for` variable or a parameter, in any code (a function's body, a class
  block, a constant's value). The top level has no name or path, so a
  top-level definition takes no qualifier.
- **`(local:)` and shadowing.** A local or parameter cannot be named like a
  definition around it ([Shadowing](#shadowing)); a `(local:)` one may. Its
  uses then write `(local:)X` wherever that other definition is visible: a
  bare `X` there is ambiguous, and an error. Where no other definition has
  the name, a bare `X` is the local. A `(local:)X` cannot be defined again in
  a nested scope, take a type parameter's name, or be a named parameter.
- **A class's qualified member.** `(c:)m` in class `c` beside a top-level `m`
  is allowed (an unqualified one is refused, [Shadowing](#shadowing)); a bare
  `m` in `c`'s code, where both are visible, is ambiguous.
  `(c:)m` in a class that inherits an `m` would be a second `m` (Book ch.
  10, "Methods with Same Name"): openverse keeps one member of a name per
  class and refuses it.
- **Refused.** A qualifier that is not where the definition is (`(M:)X` in
  module `M.N`, `(c:)X` on a local, `(local:)` on a member or in a `using`),
  a qualifier that names nothing, a path other than `/Verse.org/Verse`'s
  types, and `X.(c:)F` when two classes or interfaces above `X`'s class
  declare a field `F` (openverse merges them).

Qualifiers never reach the elaborator but a class's `(c:)M`: the modules'
renaming resolves every one (see
[DESIGN.md](DESIGN.md#qualified-names-one-resolver-for-every-qualifier)).

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
  least two arms must be able to wait (ch. 14: "What the compiler does
  insist on is that at least two of the arms be async"): an arm can wait
  when it calls a suspending function, method or function value outside a
  `spawn` or a `branch`.
- **`race`.** The arms start in source order; the first to end wins, and its
  value is the `race`'s (of the arms' common type). Every arm must be able
  to wait, as `sync`'s arms can (the Book's tests, "Ensure all top-level
  expressions in race/rush are async", `Concurrency.versetest:831`; the
  prose is silent): an arm that cannot is refused. An arm that ends without
  waiting, such as one that starts with `Sleep(0.0)` (which completes at
  once, as in ch. 14's example of a race resolved before its last arm
  starts), wins at once, and the arms after it never start. The losers that
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
- **`spawn`.** No `return` and no `break` but of a loop inside it is in a
  `spawn`'s code (the Book's tests, `SpawnAndTask.versetest` 876-892,
  "Can't break or return from a spawn"). `spawn{F(…)}` starts a task running the call, which must be
  of a suspends function or method (`spawn{Agent.Run()}`, also when
  subclasses override `Run`). Its receiver and supplied arguments run once
  in caller order, then omitted defaults run in declaration order, before
  starting the task. This includes defaults using receiver fields, refined
  arguments and opened types. Arguments and defaults cannot wait. The
  task runs at once up to its first wait. The value is a `task(t)`, where
  `t` is the result type at the receiver's static declaration, including
  when an override returns a narrower class. `T.Await()` waits for the task to end and
  gives its result (at once if it has ended, without waiting). A task's end
  resumes the tasks awaiting it inside its last step, before anything else
  runs, as a `Signal` resumes its waiters (below): in the order they began
  awaiting, each until it waits again or ends, each with the result (the
  Book's API, `task`'s `Await`: "Multiple awaiters are allowed and are
  resumed in the order they registered"; [the rule](research/scheduler-conformance.md#a-tasks-end-resumes-its-awaiters)).
  An awaiter is a spawned task, `Main`, a `branch` or an arm (several arms
  of one task each await on their own); one that is cancelled meanwhile (a
  `race` it lost) is not resumed. A task that ends inside a `Signal`, or
  inside another task's end, resumes its awaiters there, depth first; in a
  failure context that fails, its end and what its awaiters did are undone
  with the rest. A task awaiting itself, or two awaiting each other, wait
  for ever. A task is not tied to the
  code that spawned it: it runs until it ends or the program does. A
  `spawn` has `<transacts>`'s heap effects (`<reads>`, `<writes>` and
  `<allocates>`), besides those of the call it starts (the Book's tests:
  "spawn requires the transacts effect in addition to the effects of the
  spawned async function", `Effects.versetest:554`; the prose has spawn
  work "anywhere you can write code", ch. 14): it is allowed in any
  function whose effects allow those, immediate ones too, not in a
  `<computes>`, `<reads>` or `<allocates>` one; with `--extended-defaults`,
  also in a field's default of a class whose effects allow them (a task per
  construction that omits the field). A `spawn` may be in a failure
  context, as the Book's tests have it (assertions spawn;
  `LiveVariables.versetest:450-545` spawn in `if: …; false?`): its start,
  the task's first run included, is the context's code, so a context that
  fails undoes it, and the task never runs again; in a suspends function a
  `spawn` in a condition or a filter starts the task there (it is not a
  suspension point). A `spawn` in a `defer:` is refused (#156).
  Without a suspends `Main`, a task runs up to its first wait, and on only
  inside a `Signal` that resumes it (below).
  `T.Cancel()` (in a suspends function) cancels a task that has not ended:
  it unwinds at once, running its `defer:` blocks, or, when the task is
  running (its own code or one of its branches or `rush` losers runs: it
  cancels itself, or a task or branch started while it runs, at any depth,
  cancels it in its first run), when the code that runs waits next, or
  ends; cancelling a task while it unwinds finds it cancelled already. A
  cancelled task never resumes its awaiters: an await of it, made before
  the cancel or after it (or while it unwinds), waits for ever, without
  failing or cancelling anything (the Book's API, `task`'s `Await`: "a
  cancelled task never resumes its awaiters, so the call does not fail,
  does not error, and simply stays suspended for ever"; ch. 14 says it
  "propagates cancellation", which was openverse's reading until now). The
  awaiter can itself be cancelled (a `race` arm that loses, a branch whose
  function exits); a `Main` that awaits a cancelled task ends the program
  as a stalled `Main` does (below) once no task can run. A task asked to
  be cancelled at its next wait that ends before it waits again ends as
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
  says both "each awaiter" and "exactly one"). The woken tasks go on
  inside the `Signal`, as the Book's API has it ("resumed first, in the
  order they suspended ... Each resumed task runs until it blocks again
  before the next one is given a turn"; its tests, `Event.versetest:21-32`
  and the FORT-1088027 and FORT-1126351 cases): in the order they began
  waiting, each until it waits again or ends, all before `Signal` returns
  ([the rule](research/scheduler-conformance.md#awaiters-run-inside-signal)).
  A waiter is a spawned task, `Main`, a `branch`, an arm of a `sync`,
  `race` or `rush` (also one of the signalling task's own: an arm awaiting
  while its sibling signals is resumed inside that sibling's `Signal`), or
  a `rush` arm that goes on after its `rush`. An await made during a
  `Signal`, by a resumed task or another, waits for the next one (for a
  `sticky_event`, it gives the value at once). A `Signal` made by a resumed
  task runs its own round to the end before that task goes on (depth
  first), also on the same event, where it reaches the awaits made since
  the outer `Signal` began. An arm resumed inside a sibling's `Signal`
  that ends there wins its `race` or `rush` if it is the first to end: the
  signalling arm goes on to its next wait and is then cancelled (or, in a
  `rush`, goes on), and the arms after it never start (ch. 14,
  "Resolution Stops Unstarted Arms"); the race's value is the first
  completer's. Inside a `Signal`, and inside a task's end, only the woken
  waiters go on: a sleep that has expired is taken at its task's turn in
  the scheduler's pass (`Main`, then the tasks in the order they were
  started, arms in source order). A `Signal` from
  immediate code resumes its waiters the same way. A waiter cancelled
  before its turn (by an earlier waiter of the same `Signal`) does not go
  on, and a wait cancelled before the `Signal` (a `race` it lost) is no
  waiter; once `Main` ends, so does the program, after the task whose
  `Signal` ended it waits. A `Signal` with no one waiting is lost, and
  `Signal` itself never waits. `event()` is an event without a value (`event(void)`),
  with `E.Signal()` and `E.Await()`. A `sticky_event(t)` (or
  `sticky_event()`) is an event that keeps its last signal: an `Await`
  after a `Signal` gives that value at once. A `subscribable_event(t)` is an
  event that also calls the functions subscribed to it:
  `E.Subscribe(F)` (with `F` a function or method value of type
  `type{_(:t):void}`) gives a `cancelable`, whose `Cancel()` unsubscribes
  `F`, and `E.Signal(X)` calls each subscribed function in the order they
  subscribed (see [Readings](#readings-openverse-takes)), after the tasks
  awaiting `E` went on (the Book's API: "Subscribers ... are invoked only
  after every waiting task has been resumed"; #210). A
  function subscribed during a `Signal` is first called at the next one; a
  function cancelled during a `Signal`, by one called before it, is not
  called by it. As in the Book (ch. 14, "Transactional Behavior"), a
  `Subscribe` or a `Cancel` in a failure context that fails is undone. A
  `Signal` may be called in a failure context too, as the Book's tests do
  (`Event.versetest` signals in `<decides>` functions, and every
  assertion's body is one): what the waiters it resumes and the functions
  it calls do is rolled back with the context when it fails, as `Print`
  is, and the waiters wait again where they waited
  (`Coroutines/Concurrency.versetest:1562-1580`). With
  `--signal-no-rollback` (`openverse run`, `emit`, `check` and `core`,
  opt-in, #515: the reading of Epic's published `event` pages, which make
  `Signal` `<no_rollback>`; the Book's API gives `event`'s `Signal` no such
  effect), a program that may call an event's `Signal` from a failure
  context is refused before it runs or is emitted. A failure context is an `if`'s condition, a `for`'s clause, a
  `<decides>` function's body, `option{…}`, `logic{…}`, `not`, the left of
  `or`, a `first{…}` or a `do` expression, with everything that runs
  inside it: a `block`, a named argument's default, a `defer:`. What it
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
  again while a task ended or was cancelled, or a sleep expired inside a
  `Signal` or a task's end (so that what waits on them goes on in the same
  tick); the tasks awaiting a task's end, and an event's, go on inside it
  (above). Arms that can go on in the same tick do so in source order. `Sleep(S)`
  uses the binary64 product `T = 30·S` rounded up, `Ceil(T)`, at least
  one tick, for a supported positive finite input, also a subnormal one:
  a sleep wakes at the first tick at or after its deadline (the Book's API
  reference). `Sleep(0.0)` (and `-0.0`, which is `0.0`) completes at once,
  without suspending, as the Book's tested examples have it: it gives
  neither other tasks nor a cancellation a turn, so a loop that should
  give way sleeps a positive time (`Sleep(0.01)` is one tick). The product must
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
  task that never ends or was cancelled), it ends as `Err()` does: exit 2,
  its defers not run.
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
| Associativity of comparisons | the prose: chains "check all adjacent pairs" (ch. 1); the table: right (ch. 4); the tests: `<>` left-associative (`Associativity.versetest:9`), the others as a chain: the Book disagrees with itself ([the audit](research/readings-audit.md#comparison-chains-with-)) | chains: every adjacent pair checked, each operand evaluated once, result is the leftmost |
| Value of a successful `not e` | unspecified | `void` |
| Type of `if` without `else` | unspecified | `void` |
| A failing `for` body | unspecified (VC: the `for` fails) | the `for` fails (as in VC) |
| What a `for` undoes | its clauses are one search: what they did since the last value that reached the body is kept at the body and undone when the search ends; a failure undoes back to its own element or alternative (`FlowControl/for.versetest` 317-392, `Range.versetest` 140, 159, `SoftwareTransactionalMemory.versetest` 74-88; `08_failure.md:92`: "a failure context for each iteration of the domain clause"): **the Book decides** | the Book's, for a `for` whose generators are over ranges, arrays, maps and strings and choices of values, with no call of a function with several values in its clauses and no `if`, `case` or `or` that picks a branch with a choice; any other `for` keeps, for now, the old rule, entirely: what a generator's clauses did stays once they succeed, even when the generators after it give no value (designed, not built: [the audit](research/readings-audit.md#what-a-for-undoes); `tests/verse/for_search_old_paths.verse` pins it) |
| A failing `for` source | "When any expression in the iteration header fails, that iteration is skipped" (ch. 7); `for.versetest:317`: a failing range bound gives `array{}`: **the Book decides** | zero iterations, for an iterated source (`X : F[]`) and a range bound (`I := 1..F[]`) alike, what the source did rolled back (with what the search did since its last value, by the rule above); the `for` itself does not fail |
| `?` on other values | conflict (§6.1) | only `logic` and `?t` (the API's typed reading) |
| Output inside a failed failure context | unspecified for `Print` (the API's `log` class, another function, prints rolled-back lines prefixed "(Rolling Back)") | rolled back with the writes (transactional `Print`) |
| `Main` failing | (no entry point in the book) | exit code 1; output already printed stays |
| `return` or `break` inside a failure context | refused by the tests (`SOL-4199-BreakFromIf.versetest`, `Reachability.versetest` 12-15, `Return.versetest` 157-163; [the audit](research/readings-audit.md#return-and-break-in-a-failure-context)) | the Book's: refused ([Control](#supported)); a `break` in a `for`'s body, which the Book's tests allow and its prose refuses, stays refused |
| Comparability | `comparable` covers the primitive types, enums, structs, `<unique>` classes and containers of comparable types (ch. 4); not functions, `any`, nor classes and interfaces without `<unique>` (ch. 11, `CompareInstance.versetest:11`) | the Book's: the types it names, and a type parameter declared `subtype(comparable)`; `comparable` itself is a type ([comparable](#comparable)) |
| Inferring type arguments | not described; the tests refuse a type parameter no parameter's type determines (`ParametricFunctions.versetest` 336-374, 586, 3503), take one named in the result's function type's parameter (`:376`), and refuse one a contravariant class's parameter names (`:356`) | first-order matching against the expected result type, then the arguments; no subtyping other than `false` (matches anything) and `void` (accepts anything), and a bound's (an argument below it gives its instance); every type parameter of a source function must be given by its parameters, by the Book's variance: the expected result gives none any more ([Parametric functions](#parametric-functions), [the rule](research/book-forms-rules.md#a-type-parameter-the-parameters-determine)); a class that does not use its type parameter gives it (the Book is silent) |
| A qualifier without a `using` | "A qualifier only says which `F` is meant among the ones already in scope" (ch. 10): `(Top.M:)F` with no `using` is unknown | the qualifier is found as any name is, then the name is looked up in exactly that scope: `(M:)F` is `M.F` (#145) |
| A module's member `(M:)x` used bare in `M` beside an outer `x` | both are candidates, told apart by their parameters, else ambiguous (`ModuleDefinitions.versetest`, `vmodule` tests) | the inner one (only a qualified member may share an outer definition's name, [Shadowing](#shadowing)); in a class's code and for `(local:)`, where the tests refuse it, ambiguous |
| `ToString` of a float | the API and the tests: fixed point with six decimals (`FloatToString.versetest`, `1.000000`); ch. 2's example: `98.5` (the Book disagrees with itself: [the audit](research/readings-audit.md#tostring-of-a-float)) | the API's and the tests': six digits after the point, the exact value rounded half to even, every integer digit, the sign kept (`-0.000000`); `Inf`, `-Inf`, `NaN`; interpolation calls `ToString` (ch. 2) ([float](#float)) |
| `NaN < X` | `not (Nan < 1.0)`, `Nan = Nan` (ch. 1, ch. 2) | fails (IEEE: NaN orders with nothing); `NaN = NaN` succeeds (the Book) |
| `=` between different types | "Comparisons between different types still compile, but they always fail" (ch. 4); the empty value is one value of `logic`, `void`, `tuple()`, options, arrays, strings and maps (ch. 2) | the Book's (see [Equality and the empty value](#equality-and-the-empty-value)), at every depth and in generic code; where Verse Core cannot tell the two types' values apart (two type parameters, one and another type, a tuple of them and a string, `[]tuple(int, []int)` and `[]tuple(int, []char32)`), both operands are boxed and compared as `comparable`s ([comparable](#comparable)), so a `char32` and an `int` differ there too |
| `false` where a map is expected | prose: accepted (ch. 2); tests: refused (`Map.versetest` 343) | refused, as the tests (it equals an empty map) |
| `X?` of a logic | "equivalent to comparing against true" (ch. 4); the tests: `true?` is the empty value (`BoolQuery.versetest` 3, 4) | `true?` is `true`, not yet the tests' empty value ([empty-values.md](research/empty-values.md), 3.1) |
| `true` as a type | the type of the empty value, as `tuple()` (ch. 2); `void` and `true` interchange (`Void.versetest`); `Result:true = branch: …` refused, `Result:any = branch: …` valid (`FORT-582630-BranchResult.versetest`) | the Book's: `tuple()`; `void` and it interchange inside options, arrays and maps; a `branch:`'s value is an `any` ([the rule](research/book-forms-rules.md#true-as-a-type)); not yet in a function type (`int->true` and `int->void` are two types) |
| Ordering of rationals | not stated (§2 lists `<` … for `int` and `float`) | exact (by continued fractions, so it cannot overflow), and an int compares with a rational |
| Order of a choice's values | (not in the Book; the Verse Calculus: spatial) | spatial: the leftmost choice varies slowest, as nested generators do (#208) |
| Code before a choice | (the Verse Calculus is pure) | runs once, also within an expression (the operands before the choice are evaluated first, as written); each alternative runs the code after the choice, from where the choice was reached; in an `if` or `first{}`, one that leads to no success is rolled back (as backtracking does); in a `for` too, one none of whose values reaches the body (the Book's rule for a `for`, above, a choice being one more choice point); a `for` that keeps the old rule for now rolls back only an alternative whose own clauses fail (#208): **the Book is silent** on choice |
| A choice in an operand of `and` or `or` | not stated (the left of `or` is a failure context, the right is not, §6.2) | `A and B`: `A`'s clauses, then `B`'s, in the context the `and` is in, so `B`'s values for each of `A`'s; `A or B`: `if (T := A) then T else B`, so the left's first success, if it has one, is the only value (the right is not tried when what follows fails), else the right's values, taken by the context the `or` is in (all of them in a `for`), not only its first (#283) |
| A call of another function with several values in a recursive one's code | not stated (the Verse Calculus: a call is its body) | a choice point of the recursive one, taken with it: when the callee's clauses fail it has no values (#283); in a `for`, which keeps the old rule for now when it takes such a call, what came before the call stays, as at a call of the recursive one itself, not undone as at an inlined call: **the Book is silent** |
| A `defer:` in a function with several values, or in a block of its code | not stated (ch. 7: it runs when its scope exits) | it runs as each value leaves the scope, after the value is computed and before the code after the call or the block, and at a `return` after the return's value; a call or a block whose clauses fail gives no value and runs none; in a `for`, what it does is part of that value's code, undone with it when a later filter rejects the value, whether the call is inlined or taken lazily (#283): **the Book is silent** |
| A recursive function with several values whose only calls of itself are in failure contexts of its own code | not stated (the Verse Calculus: a call is its body) | inlined, as a function recursive only through another function that consumes it is (the contexts are functions of their own): where its clauses fail in a `for`'s clauses (which keeps the old rule for now, as any `for` taking a call of a function with several values), what those clauses did since their last generator is undone with them, as for any inlined call, not kept as at a lazily taken call, which is a generator of its own (#283): **the Book is silent** |
| A clause of a `for` with a choice in it | (the Book has no choice; ch. 7: "Each filter must be failable") | a generator over its values, as a clause that calls a function with several values is: not a filter, so it need not fail (`for (X := 1..2, set N = (1 \| 2))` runs the body for each value); the statements of a function with several values that a `for` takes are the function's, not the `for`'s filters |
| Precedence of `\|` | (not in the Book) | below `+`, above the comparisons: `X = 1 \| 2` is `X = (1 \| 2)` (#208) |
| `Sleep(0.0)` | "may resume in the same tick" (ch. 14), "One frame" (ch. 14); the API reference: it always yields; the tested ch. 14 examples (`03`, `05` to `11`): it completes at once, in a `race`, a `sync` and plain code: the Book disagrees with itself ([the rules](research/scheduler-conformance.md#sleep00-completes-at-once)) | the tested examples': completes at once, without suspending, as a negative or NaN duration does |
| `Sleep(S)` rounding | the API: "a sleep resumes on the first update at or after its deadline and never sooner than the next one. Short sleeps therefore round up"; no tick rate | the first tick at or after the deadline: the binary64 product `30·S` rounded up, at least one tick (`Sleep(0.04)` takes 2 ticks; `Sleep(0.1)`, whose product is exactly 3.0, 3); bounded inputs and checked clock accumulation follow the explicit reference policy above (#514) |
| End of a program with tasks | not stated | the program ends when `Main` does; a `Main` that waits with no task able to run is an error (exit 2) (#156) |
| Order of a `subscribable_event`'s functions | the API: "invoked in a randomised order on every signal", "only after every waiting task has been resumed"; ch. 14's example lists them in subscription order | subscription order, after the tasks awaiting the event went on inside `Signal` (#210) |
| Event waiter resumption | the Book's API: awaiting tasks "resumed first, in the order they suspended", each until it blocks before the next, and `Signal` "returns before the resumed tasks have finished"; its tests have awaiters run inside `Signal` (`Event.versetest:21-32`, FORT-1088027, FORT-1126351) | the Book's: inside `Signal`, in the order they suspended, each until it waits again or ends, the same task's arms included; an await made meanwhile joins the next `Signal`; nested `Signal`s depth first (#513, [the rule](research/scheduler-conformance.md#awaiters-run-inside-signal)); a task's end resumes its awaiters inside it the same way, in the order they registered (the API's `task`, `Await`; [the rule](research/scheduler-conformance.md#a-tasks-end-resumes-its-awaiters)) |
| Awaiting a cancelled task | the API (`task`, `Await`): "a cancelled task never resumes its awaiters, so the call does not fail, does not error, and simply stays suspended for ever"; ch. 14: "it propagates cancellation: if the awaited task was canceled, `Await()` passes that cancellation on to the caller"; the tests decide neither (`SpawnAndTask.versetest:342-355`); `Cancel` itself is unreleased (ch. 14) and `<epic_internal>` (the API): the Book disagrees with itself | the API's: the await waits for ever; the awaiter can be cancelled itself (a `race` it loses); a `Main` stalled on one ends the program with exit 2 ([the cancelled task](research/scheduler-conformance.md#the-cancelled-task)) |
| Signal in a failure context | the Book's tests signal in `<decides>` functions and assertions and expect success (`Event.versetest` 64-119); a failed context undoes the resumption (`Coroutines/Concurrency.versetest:1562-1580`); the Book's API gives `event`'s `Signal` no `<no_rollback>` (Epic's published pages do) | the tests': allowed, and what it and the awaiters it resumed did is rolled back with a failing context; `--signal-no-rollback` refuses it, as Epic's pages read (#515) |
| Extent of a `<#>` comment | "everything indented by four spaces on subsequent lines" (§1.1) | the rest of the `<#>` line and every following line indented more than that line, whatever the amount (blank lines included); `<#>` may also follow code on a line |

## Not supported in v1

`ToString` of rationals (see [rational](#rational)), float functions beyond those of [float](#float), the class features listed under [Classes](#classes), struct methods (Verse structs have none; classes do),
what [Weak maps](#weak-maps) and [comparable](#comparable) list as not yet, module paths `using{/Verse.org/…}` (accepted and ignored), paths as values and path qualifiers other than `(/Verse.org/Verse:)` of a built-in type, two members of one name in a class (`(c:)M` beside an inherited `M`, Book ch. 10), the
specific overload/call gaps listed under [Overloading](#overloading), nested
functions and lambdas (a lambda, `(X:int) => X`, `a => b`, parses, as the Book's tests have it, and is refused; see [release evidence and proposed design](research/closure-design.md)),
pointers (`e^` and `^t` parse, as the Book's tests have them, and are refused: the Book's chapters define none), specifiers on a macro's name (`for<par>(…)`, parsed and refused, 3604), declarations with no body (`F():void`, `X:int` on their line: parsed and refused, as openverse has no definitions made elsewhere), choice beyond [Choice](#choice), concurrency beyond [Concurrency](#concurrency), and the unsupported
effect/construction contracts listed under [Effect contracts](#effect-contracts).
