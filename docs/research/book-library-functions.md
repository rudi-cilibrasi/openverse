# Library functions the Book's tests call

The Book's test suite calls built-in functions openverse lacked: the
conversions of characters, `Clamp`, `Sgn`, `IsFinite` as a method, math
functions used as values, and the bitwise functions. This note pins what
each is, from the Book at
[`beaa719`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0)
(its chapters, and its Runtime API reference `docs/api/verse_runtime_api.html`,
which says it is generated from the Verse runtime) and from Epic's published
Verse API pages, and says what openverse does with it. No Epic source code
was read. Case counts are those of [the survey](book-test-conformance.md).

## Character conversions

The API reference, section "char and char32", declares six extension
methods; Epic's page for
[`ToChar`](https://dev.epicgames.com/documentation/en-us/fortnite/verse-api/versedotorg/verse/tochar)
gives the same declaration without prose. The Book's ch. 2 (`02_primitives.md`,
"Characters") says only that `char` is a UTF-8 code unit and `char32` a
code point.

| Declaration | Result | Fails | openverse |
|---|---|---|---|
| `(Byte:char).ToCodeUnit()<converges><predicts>:int` | "the numeric value of a UTF-8 code unit, 0 to 255" | never | a binary search of eight char comparisons over the table of the 256 chars |
| `(Character:char32).ToCodePoint()<converges><predicts>:int` | the code point; "total: a char32 is a Unicode scalar by construction" | never | the same int (a char32 is an int in Verse Core) |
| `(Value:int).ToChar()<converges><decides><predicts>:char` | the char of that code unit | "when the number is not a valid UTF-8 code unit"; the tests: below 0 and above 255 (`Intrinsics/CharConversionExtensionMethods.versetest:49-55`) | an index into the table, which fails outside it |
| `(CodePoint:int).ToChar32()<converges><decides><predicts>:char32` | the char32 of that code point; "unassigned code points and the designated non-characters" are accepted | "negatives, anything above 0x10FFFF, and the UTF-16 surrogate range 0xD800 to 0xDFFF" | three comparisons |
| `(Byte:char).ToAsciiChar32()<converges><decides><predicts>:char32` | the char32 of the same number | "for any byte above 127", which is part of a multi-byte sequence | a comparison with the char 128, then the code unit |
| `(Character:char32).ToAsciiString()<converges><predicts>:[]char` | "encodes any Unicode scalar as UTF-8, emitting between one and four char values" | never | the encoding `ToString` of a char32 already used |

They are methods of their receivers, called with `()` when they cannot fail
and with `[]` when they can ("Written N.ToChar32[]: it is <decides>, so the
square brackets are required"). The test file marks them VerseVM-only and
expects BPVM to refuse them (`assert_semantic_error(3506)`); openverse
follows the API reference. The survey's "character conversions" cause (147)
was mostly not these: 145 cases of `Literals/Char.versetest` call free
functions `ToChar(N)` and `ToChar32(N)` with parentheses, as total functions
(`RequireChar8Equal[HexLiteral, ToChar(Utf8CodeUnit)]`). Neither the API
reference nor Epic's pages declare such functions, a `<decides>` method
cannot be called with `()`, and the file uses the test runner
(`using { /Verse.org/Tests/VerseTestScriptCmd }`): they are most likely the
test runner's, and openverse does not invent them.

## Clamp, Sgn, IsFinite

| Declaration | Source | Rule | openverse |
|---|---|---|---|
| `Clamp<native><public>(Val:int, A:int, B:int)<computes><predicts>:int` | API reference, "Math"; [Epic](https://dev.epicgames.com/documentation/en-us/fortnite/verse-api/versedotorg/verse/clamp-1) | "the median of the three arguments … the order of A and B does not matter: Clamp(5, 2, -2) and Clamp(5, -2, 2) both give 2" | median by comparisons |
| `Clamp<public>(Val:float, A:float, B:float)<computes><dictates>:float` | [Epic](https://dev.epicgames.com/documentation/en-us/fortnite/verse-api/versedotorg/verse/clamp); the API reference mentions "the float version, where NaN behaves as though it were greater than +Inf" | "the median of Val, A, and B, such that comparisons with NaN operate as if NaN > +Inf" | median by a comparison that orders NaN last: `X ≤ Y` holds when Verse Core's `fle` does (it holds of a NaN and itself), or when `Y` is not below +Inf |
| `Sgn<public>(Val:int)<computes><dictates>:int` | [Epic](https://dev.epicgames.com/documentation/en-us/fortnite/verse-api/versedotorg/verse/sgn) | 1, 0 or -1 | two comparisons |
| `Sgn<public>(Val:float)<computes><dictates>:float` | [Epic](https://dev.epicgames.com/documentation/en-us/fortnite/verse-api/versedotorg/verse/sgn-1); the API reference's `ArcTan` uses `Sgn` of infinities | 1.0, 0.0, -1.0, "NaN if Val = NaN"; the tests: `Sgn(-Inf) = -1.0`, `Sgn(Inf) = 1.0` (`Math/Math.versetest:179-181`) | two comparisons; NaN and zero are their own sign |
| `(X:float).IsFinite<public>()<computes><decides><dictates>:float` | [Epic](https://dev.epicgames.com/documentation/en-us/fortnite/verse-api/versedotorg/verse/isfinite) | "Returns X if X is finite. Fails if X is one of +Inf, -Inf, NaN" | `F.IsFinite[]` is openverse's `IsFinite[F]` |

`Clamp` and `Sgn` evaluate each argument once, in order, and are soft
built-ins: a program may define its own (`Math.versetest`'s `SgnF` is "a
hack to avoid ambiguous overload resolution"). Over -Inf, -2, -0.5, 0, 1, 2,
Inf and NaN, all 512 float `Clamp` triples and the 8 `Sgn` values agree with
a Python model of the rules above, in Lean and in C.

## Built-ins as values

The tests pass built-ins to function parameters: `CheckSpecials[Sin, NaN,
NaN]` with `CheckSpecials(F(:float):float, …)` (`Math/Math.versetest`, 29
cases). The API reference says of the compiler's intrinsics that "most
cannot be referenced as first-class values"; the math functions are
declared `<native>`, not intrinsics, and the tests pass them. openverse's
rule: a built-in of one signature is a function like any other. Where a
program names one as a value and neither defines nor binds that name, it
gets an ordinary definition `Sin(X0:float)<computes>:float = $Sin(X0)`,
with the built-in's effects, and `FnValues` makes it a value as it makes any
function one (`OpenVerse/Front/BuiltinValues.lean`). `$F` names the built-in
`F` whatever the program defines, as the concurrency prelude's `$Round`
already did. The built-ins of one signature are `Sqrt`, `Exp`, `Ln`, `Sin`,
`Cos`, `Tan`, `ArcSin`, `ArcCos`, `Pow`, `Log` (`<computes>`); `Sinh`,
`Cosh`, `Tanh`, `ArSinh`, `ArCosh`, `ArTanh`, `Lerp` (`<reads>`, as #490
gave them); `IsFinite`, `Round`, `Int` (`<computes><decides>`). Overloaded
ones (`Abs`, `Min`, `Max`, `Floor`, `Ceil`, `ArcTan`, `Clamp`, `Sgn`,
`ToString`), generic ones (`Concatenate`, `ConcatenateMaps`) and those a
program may not define (`Quotient`, `Mod`, `Print`, `Err`) are refused as
values. `Quotient` and `Mod` are of one signature: making them soft
built-ins would let them be values, and let programs define them, which is
a decision of its own.

## What is left of "other library functions"

| Name | Cases | Source | What it needs |
|---|---:|---|---|
| `GetCastableFinalSuperClass`, `…FromType` | 15 | API reference; `<castable>` and `<final_super>` classes | the class specifiers of #11 |
| `FitsInPlayerMap` | 3 | API reference, persistence: "Succeeds when Value is something a player's persistent map is allowed to hold" | persistence (engine) |
| `GetSecondsSinceEpoch` | 2 | listed in the API reference's module index; the tests check two calls in one transaction agree and the value is after 2024 | a clock: openverse is deterministic, so a new Core primitive and a stated source of time |
| extension methods `PlusTwo`, `TestParametricExtensionMethod` | 2 | the test runner's, as its `TakeExtension` is (`ExtensionFields.versetest:157`) | not translatable since [extension methods](extension-methods.md) were built |

12 cases used `Pow2_52`, `Pow2_Minus25` and `Pow2_Minus28`, constants of
the test runner's `FloatConstants` module that the files `using`; the
survey's harness now counts them not translatable, as it counts the other
`FloatConstants` cases.

## Bitwise functions (not implemented)

**What the Book says.** Ch. 4, "Bitwise Operations" and "Bit Shift
Operations" (`04_operators.md:133-309`): `BitAnd`, `BitOr`, `BitXor` and
`BitNot` "operate on the two's complement binary representation of
integers", only on `int`; `BitNot(X) = -X - 1`; "On the Verse VM, bitwise
operations support arbitrarily large integers (bignums beyond 2^64). On the
Blueprint VM, values must fit within the 64-bit signed integer range".
`BitShiftLeft[X, N]` and `BitShiftRight[X, N]` are failable: "they fail
when the shift count is negative"; both are arithmetic ("A negative value
shifted right rounds toward negative infinity"); shifting right by a count
at least as wide as the value leaves "0 for non-negative values and -1 for
negative ones"; "Integers in Verse are arbitrary precision, so shifting left
grows the result beyond 64 bits". The API reference declares
`BitAnd(Lhs:int, Rhs:int)<converges><predicts>:int` and the others alike,
"two's-complement bit patterns of unlimited width. Negative values behave as
though sign-extended forever to the left", available from Fortnite 4200;
it does not list the shifts (the tests make them available from 4400).
Epic's [BitAnd page](https://dev.epicgames.com/documentation/en-us/fortnite/verse-api/versedotorg/verse/bitand)
gives `BitAnd(Lhs:int, Rhs:int):int` and no prose.

**What the tests say** (`Math/Bitwise.versetest`, 159 refused cases): 84
untagged cases within int64 (and the failing negative counts); 13
`bp_vm_only` cases expecting the runtime error `MathIntrinsicCallFailure`
for operands or results outside int64 (`BitShiftLeft[1, 63]`,
`BitAnd(9223372036854775807 + 1, 1)`); 62 `verse_vm_only` cases assuming
unbounded integers (`BitShiftLeft[1, 64] = (0x7FFFFFFFFFFFFFFF + 1) * 2`,
`Pow2_64` operands, a shifted width limit of 2^20 bits that is a runtime
error beyond). Under openverse's BPVM reading of `int`, the untagged and
`bp_vm_only` cases can agree (an overflow is openverse's runtime error);
most `verse_vm_only` cases would become different results, as the 26
`int`-precision cases are, because their own operands overflow.

**Two ways to add them.**

- *With Verse Core's existing operations*, as the character conversions
  are: `BitNot(X)` is `-1 - X` (which cannot overflow); `BitShiftLeft[X,
  N]` is `X * 2^N` with the multiplication's overflow check (a count above
  62 overflows unless `X = 0`), failing on `N < 0`; `BitShiftRight[X, N]`
  is `Floor(X / 2^N)` (`floorDiv`), `0` or `-1` from `N = 63` on;
  `BitAnd`, `BitOr`, `BitXor` take the two's complement bits by 64 steps of
  `Mod[X, 2]` and `Floor(X / 2)` (Euclidean and flooring, so the bits of a
  negative number are its two's complement) and rebuild the result from
  the top bit down, the sign bit weighing -2^63. No Core, proof, OVBC or
  runtime change; each `BitAnd` costs some hundreds of Core steps, and
  fuel.
- *As primitives*: six `Prim` constructors with their semantics in
  `Core/Prims.lean` (`Int.land`, `Int.lor`, `Int.xor`, `Int.not`, and shifts
  with the int64 range check of the other operations), their typing in
  `Core/TypeCheck.lean` and `Core/Typing.lean` and the cases of the type
  safety proof (`Core/TypeSafety.lean`), opcodes 65 to 70 in
  `Core/Encode.lean` and `docs/FORMAT.md` (older runtimes reject them),
  their C in `runtime/src/prims.c` or `arith.c`, the QuickProof law
  `proofs/quickproof/arith` extended to the shifts' overflow conditions and
  the Lean seams of `Core/Seams.lean` (`docs/SEAMS.md`, section 1), and the
  differential fuzzers. This is the owner's decision; the unbounded
  `verse_vm_only` behaviour would need unbounded integers in Core and the
  runtime, which no part of openverse has.
