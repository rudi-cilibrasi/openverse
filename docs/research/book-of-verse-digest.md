# Book of Verse: Core Semantics Digest

This digest supports a clean-room reference implementation (Lean 4 semantics plus a C interpreter).

- **Primary source:** *Book of Verse*, https://verselang.github.io/book/ (chapters 00–18). The chapter pages carry "last update" stamps; the overview's is 2026-09-15. Retrieved 2026-11-03.
- **Epic mirror:** https://dev.epicgames.com/documentation/en-us/fortnite/verse-language-book-of-verse-reference. It is only a stub page that links to verselang.github.io and https://github.com/verselang/book.
- **Secondary source:** the book's *Runtime API Reference*, https://verselang.github.io/book/api/verse_runtime_api.html. It is linked from the Primitives chapter and is "Produced by `bin/verse_api` from the Verse runtime in fortniteMain (UE 6.0.0)". This digest cites it as **[API]** wherever it answers something the prose chapters leave open.
- **Calculus:** Augustsson et al., *The Verse Calculus*, ICFP 2023 (extended version). This digest cites it as **[VC]**. It is used only in §6.9 and §7.8.

Conventions used in this digest:

- `> "..."` is a verbatim quote.
- **UNSPECIFIED in book** means the prose chapters do not say.
- **CONFLICT** marks a place where two parts of the book disagree.
- Book code samples routinely use bare failable lines such as `Doubled = array{20, 40, 60}` as inline checks. The overview calls one of them "the assertion that follows the failed purchase" (https://verselang.github.io/book/00_overview/#an-example). Treat these lines as test assertions, not as a statement that top-level failable code is legal. What a failable expression means at module top level is UNSPECIFIED in the book.
- The landing page warns: > "The documentation pertains to the head of the main development branch of Verse, some features may be discussed before they are officially released and are thus subject to change." (https://verselang.github.io/book/)

---

## 1. Lexical structure

### 1.1 Comments
Source: https://verselang.github.io/book/00_overview/#comments

```verse
CriticalDamage := 100.0 * 1.5   # Apply critical hit multiplier
Result := BaseValue <# original amount #> * Multiplier <# scaling factor #> + Bonus
<# Temporarily disabled for testing
   OriginalFunction()  <# This had a bug #>
#>
<#>
    This entire block is a comment because it is indented.
DoSomething()  # Not part of the comment.
```

- A line comment starts with `#` and runs to the end of the line.
- `<# ... #>` is a block comment, usable inline or across lines. > "Block comments nest".
- `<#>` on its own line starts an indented comment: > "everything indented by four spaces on subsequent lines becomes part of the comment".
- Comments inside string literals are stripped. Source: https://verselang.github.io/book/01_expressions/#string-literals

  ```verse
  Text := "abc<#comment#>def"
  Text = "abcdef"
  ```

- Whether an unescaped `#` inside a string starts a comment is UNSPECIFIED in book. The escape `\#` exists, which suggests it might.

### 1.2 Identifiers
Source: https://verselang.github.io/book/01_expressions/#identifiers-and-references

> "An identifier begins with a letter (A-Z, a-z) or an underscore (`_`), and its subsequent characters are letters, digits (0-9), or underscores. The single underscore `_` is reserved and cannot be used as an identifier."

> "Identifiers are case-sensitive and use only ASCII characters—Unicode characters are not supported in identifiers."

> "The language does not syntactically distinguish between different kinds of identifiers (types, functions, variables)—the context determines how each identifier is used."

- Naming conventions are not enforced: PascalCase for values and functions, snake_case for types (https://verselang.github.io/book/00_overview/#naming-conventions).
- The book never gives a list of reserved keywords, so that list is UNSPECIFIED in book.
- Keywords can be used as enum values through qualification, e.g. `(keyword_enum:)for` (https://verselang.github.io/book/09_structs_enums/#explicit-qualification).

### 1.3 Integer literals
Source: https://verselang.github.io/book/01_expressions/#integer-literals

```verse
Count := 42
Large := 9223372036854775807         # Maximum 64-bit signed integer literal
Byte := 0xFF                         # Hexadecimal
LowercaseHex := 0xabcdef             # Either case of hex digit works
```

> "Integer literals must fit within a 64-bit signed integer range (`-9223372036854775808` to `9223372036854775807`). This is a compile-time restriction on what values you can write directly in your code."

The book lists `Negative := -17` among its literal examples and also lists unary `-` as a prefix operator (https://verselang.github.io/book/04_operators/#prefix-operators). Whether `-` belongs to the literal or is a prefix operator, and so whether `-9223372036854775808` is one literal or the negation of an out-of-range literal, is UNSPECIFIED in book.

### 1.4 Float literals
Source: https://verselang.github.io/book/01_expressions/#float-literals

```verse
Pi := 3.14159
Explicit := 12.34f64    # Explicit bit-depth suffix
Large := 1.0e10
Small := 1.0e-5
WithSign := 2.5e+3
```

> "Float literals must include a decimal point (`1.0` is valid, but `1` is an integer). A final decimal point without digits is invalid (`1.` is a syntax error). All floats are 64-bit (IEEE 754 double precision); the `f64` suffix is optional."

A literal outside the double range, such as `1.7976931348623159e+308`, is a compile-time error.

### 1.5 Character literals
Sources: https://verselang.github.io/book/01_expressions/#character-literals and https://verselang.github.io/book/02_primitives/#characters-and-strings

```verse
LetterA := 'a'          # char (ASCII)
Emoji := '😀'           # Non-ASCII automatically char32
E :char = 0o65          # same as 'e'
F :char32 = 0u00E9      # same as 'é'
```

- `char` is > "a single **UTF-8 code unit**". `char32` is a Unicode code point.
- ASCII literals (U+0000–U+007F) have type `char`; non-ASCII literals have type `char32`. > "No implicit conversion between `char` and `char32`". Verse also > "does not allow implicit conversion between characters and integers".
- `0oXX` is "hexadecimal notation" for `char`, despite the `o`. `0uXXXXXX` is hexadecimal for `char32`, ranging up to `0u10ffff`.
- Escapes, valid in both chars and strings: `\t \n \r \" \' \\ \{ \} \< \> \& \# \~`.
- > "Character literals cannot be empty or contain multiple characters."

### 1.6 String literals and interpolation
Sources: https://verselang.github.io/book/01_expressions/#string-literals and https://verselang.github.io/book/02_primitives/#characters-and-strings

```verse
Message := "Hello, {Name}!"
Info := "Age next year: {Age + 1}"                      # Any expression
LongMessage := "This is a multi-line {
}string that continues across {
}multiple lines."
Text1 := "ab{}cd"
Text1 = "abcd"
```

- `string` is an alias for `[]char`: > "strings are byte sequences rather than Unicode character sequences". So `"José".Length = 5`, and `"abc" = array{'a', 'b', 'c'}` succeeds.
- Interpolation: > "Interpolation works for any value that has a `ToString()` function in scope." It > "implicitly calls `ToString()`" (https://verselang.github.io/book/02_primitives/#tostring).
- `ToString` has overloads for `int`, `float`, `char` and `string` only: > "`ToString()` only works on primitive types."
- Empty interpolants, including ones that contain only a newline, are ignored.
- Literal braces must be escaped as `\{` and `\}`.
- Ints beyond 64 bits > "cannot be used in string interpolation or persisted" (https://verselang.github.io/book/02_primitives/#integers).
- [API] `ToString(float)` always prints fixed point with exactly six decimal places, for example `"Float: 3.140000"` (https://verselang.github.io/book/api/verse_runtime_api.html, `float_util`/`int_util` sections).

### 1.7 Other literals
- `true` and `false` are the `logic` literals (https://verselang.github.io/book/01_expressions/#boolean-literals).
- Path literals look like `/Verse.org/Verse` (https://verselang.github.io/book/01_expressions/#path-literals).
- `false` is also the empty option, the empty array or map, and the unit value. See §4.10.

---

## 2. Expressions, blocks and sequencing

### 2.1 Everything is an expression
Source: https://verselang.github.io/book/01_expressions/

> "Everything in Verse is an expression: every piece of code produces a value, including constructs that in other languages would be statements. An `if`, a loop, a variable declaration, and a block all evaluate to something."

### 2.2 Block value
Sources: https://verselang.github.io/book/01_expressions/#compound-and-block-expressions and https://verselang.github.io/book/07_control/#blocks

```verse
Result := {
    Temp := ComputeIntermediate()
    Adjustment := CalculateAdjustment(Temp)
    Temp + Adjustment
}
FinalScore := block:
    Base := CalculateScore()
    Base + Bonus + Accuracy       # This becomes the block's value
```

- > "The value of a compound expression is the value of its last sub-expression."
- > "Compound expressions create new scopes for variables".
- `block:` is the keyword form.

### 2.3 Three or four syntactic styles
Sources: https://verselang.github.io/book/00_overview/#syntactic-styles and https://verselang.github.io/book/07_control/#blocks

```verse
Braced := if (Score > 90) { "excellent" } else { "needs improvement" }
Indented := if (Score > 90):
    "excellent"
else:
    "needs improvement"
Inline := if (Score > 90) then "excellent" else "needs improvement"
Dotted := if (Score > 90). "excellent" else. "needs improvement"
```

- > "Use four spaces to indent code blocks… The colon at the end of a line introduces a block, and the lines indented beneath it are the contents of that block" (https://verselang.github.io/book/00_overview/#code-formatting).
- The styles can be mixed (`if:` … `then { } else { }`).
- The precise offside rule is UNSPECIFIED in book: whether exactly four spaces are required, whether tabs are allowed, and what happens with dedents or continuation lines.

### 2.4 `;`, `,` and newline separators
Source: https://verselang.github.io/book/01_expressions/#semicolons-vs-commas

```verse
Sequence := (1; 2; 3)     # Evaluates 1, then 2, then 3
Sequence = 3              # And returns the last one
# Sequence := 1; 2        # ERROR: parentheses are required
Tuple := (1, 2, 3)        # Creates a tuple of three elements
Result := MultiplyByTen(2; 3)     # Discards 2, then calls MultiplyByTen(3)
Lines := (
    1
    2
    3
)
Lines = 3        # Same as (1; 2; 3)
```

- > "Semicolons within parentheses create *sequences*: they evaluate expressions in order and return the value of the last expression."
- > "Commas within parentheses create *tuples*".
- > "Newlines behave like semicolons - they create sequences".
- `array{1, 2; 3}` and `for (X := 1..3, X <> 2; X <> 3)` are errors: separators cannot be mixed.
- `option{1, 2}?` is `(1, 2)`, while `option{1; 2}?` is `2`.
- **CONFLICT (braces with commas).** One passage says > "Within block expressions (braces), semicolons and commas are interchangeable as separators between definitions". The same chapter later shows `Comma := { A, B, C }  # Comma separation (returns tuple (A, B, C))`. A plausible reading: commas between *definitions* only separate them, while commas between plain *values* build a tuple. The book does not state this rule.

### 2.5 Evaluation order
- Argument order is defined: > "Positional arguments: Left to right… Named arguments: Left to right as encountered… Default values: Filled in for omitted parameters, left to right in parameter order" (https://verselang.github.io/book/06_functions/#evaluation-order).
- Range bounds: > "Left bound evaluated first, then right bound… Both bounds always evaluated, even if the range is empty" (https://verselang.github.io/book/07_control/#range-iteration).
- `set`: > "Verse evaluates the left-hand side of `set` before the block executes" (https://verselang.github.io/book/05_mutability/#set-with-block-expressions).
- Order of evaluation for binary operator operands is not stated explicitly beyond "left-to-right" grouping: UNSPECIFIED in book.

---

## 3. Definitions, mutation and scoping

### 3.1 Constants
Sources: https://verselang.github.io/book/04_operators/#assignment-and-initialization and https://verselang.github.io/book/01_expressions/#assignment-and-binding

```verse
MaxHealth:int = 100
PlayerName:string := "Hero"
AutoTyped := 42  # Inferred as int
Z := W := 10      # Right-associative chaining
```

> "When initializing constants and variables, both `=` and `:=` can be used if an explicit type is provided. For type inference (no type annotation), you must use `:=`."

`:=` is right-associative and has precedence 1, the lowest.

### 3.2 Variables
Sources: https://verselang.github.io/book/05_mutability/#requirements-for-var-declarations and https://verselang.github.io/book/05_mutability/#var-declarations-as-expressions

```verse
var Health:float = 100.0    # A var needs both an explicit type and a value
# var Health := 100.0       # ERROR: := cannot be used with var
# var Health:float          # ERROR: no initial value in a local scope
X := (var Y:int = 42)      # X is 42, and Y is declared and mutable
```

- `var Score:int := 0` is also accepted (https://verselang.github.io/book/04_operators/#assignment-and-initialization).
- Class and interface `var` fields may omit the initializer.
- > "Variable declarations with `var` can be used as expressions, evaluating to their initial value".
- Effects: > "Reading from a `var` variable requires the `<reads>` effect. Using `set` requires both `<reads>` and `<writes>` effects." The Effects chapter adds: > "the `set` instruction is by default `<transacts>` due to the addition of *live variables*" (https://verselang.github.io/book/13_effects/#heap-effects).

### 3.3 `set` and compound assignment
Sources: https://verselang.github.io/book/01_expressions/#set-expressions, https://verselang.github.io/book/01_expressions/#assignment-and-binding and https://verselang.github.io/book/04_operators/#compound-assignments

```verse
set Health = 10
set Hero.Count = 5
set Slots[0] = 99
set Scores["Ana"] = 3
set Y = set X = 5  # Both X and Y become 5
set Values[Inc()] += 1   # Inc() runs once
```

- > "Set expressions are themselves expressions that **return the value being assigned** (the right-hand side)."
- [API] Compound operators `+= -= *=` evaluate "to the new value".
- > "Compound assignment operators evaluate the left-hand side expression only once".
- Allowed compound operators:
  - `set +=` on `int`, `float`, `string` and arrays.
  - `set -=` and `set *=` on `int` and `float`.
  - `set /=` on `float` only. `set Count /= 2` on an int is a compile error > "because integer division is failable".
- Tuple elements cannot be assigned. `set T(0) = 70` is an error (https://verselang.github.io/book/05_mutability/#tuple-mutability-replacement-only).
- Mutation paths must be `var` all the way down. Fields of a struct are mutable through a `var` variable only if the struct is `<computes>`: > "Only structs marked `<computes>` (pure structs) allow field mutation through a variable" (https://verselang.github.io/book/05_mutability/#only-structs-allow-field-mutation).

### 3.4 Scoping and shadowing
Sources: https://verselang.github.io/book/05_mutability/#scope-and-redeclaration-restrictions and https://verselang.github.io/book/07_control/#if-expressions

```verse
var Count:int = 0
# Count := 1             # ERROR: Count exists; write `set Count = 1` instead
if (SomeCondition?):
    # Count := 2         # ERROR: no shadowing, not even in a nested scope
```

- > "Verse does not allow variable shadowing. Once an identifier is declared, you cannot redeclare it with `:=` anywhere in the same scope or any nested scope."
- Locals also cannot shadow class members (https://verselang.github.io/book/10_classes_interfaces/#restrictions).
- `(local:)X` qualification exists for collisions with module members (https://verselang.github.io/book/16_modules/).
- `if` condition bindings: > "Variables defined in the condition are available in the `then` branch but not in the `else` branch."
- Bindings inside `and`/`or`/`not`: > "Variable bindings do not escape from logical operations… those bindings are only evaluated for short-circuit control flow and are **not** accessible afterward" (https://verselang.github.io/book/01_expressions/#logical-operations).
- Nested functions > "cannot reference variables or other nested functions defined later in the same scope" (https://verselang.github.io/book/06_functions/#restrictions).
- Forward references between module-level definitions are UNSPECIFIED in book.
- Sibling blocks can reuse a name; the book's own examples redefine `X` in successive `block:`s (https://verselang.github.io/book/01_expressions/#in-specific-scopes). An explicit rule is UNSPECIFIED in book.

### 3.5 Value versus reference semantics
Source: https://verselang.github.io/book/05_mutability/#deep-vs-shallow-mutability

- > "This deep-copy semantics extends to all value types: structs, arrays, maps, and tuples."
- > "**structs in collections are copies, classes in collections are shared references**."
- `set D[0] = 3` > "is compiled into `set D = array{3,D[1],D[2]}`" (https://verselang.github.io/book/03_containers/#arrays).

---

## 4. Types

### 4.1 `int`
Sources: https://verselang.github.io/book/02_primitives/#integers and https://verselang.github.io/book/02_primitives/#overflow-and-vm-differences

> "At runtime, integers are arbitrary precision and can grow beyond any fixed size."

Overflow depends on the VM:

> "**VerseVM** uses arbitrary precision. Arithmetic that would exceed 64 bits simply produces the larger value."
> "**BPVM** uses 64-bit integers and raises a runtime error (`MathIntrinsicCallFailure`) on overflow — including via `+=`, `*=`, unary negation of the minimum value, and the bitwise intrinsics."
> "Code that must behave identically on both VMs should stay inside the signed 64-bit range."

[API] On BPVM the overflow is > "an error, not a failure, so it cannot be recovered from". On VerseVM, `+` > "can never overflow". Source: https://verselang.github.io/book/api/verse_runtime_api.html#int

`BitShiftLeft[1, 64] = (9223372036854775807 + 1) * 2  # 2^64` is shown as valid (https://verselang.github.io/book/04_operators/#bit-shift-operations).

### 4.2 `float`
Sources: https://verselang.github.io/book/02_primitives/#floats and https://verselang.github.io/book/01_expressions/#float-literals

> "A float is an IEEE 64-bit float… The implementation differs from the IEEE standard in the following ways: There is only one `NaN` value. `NaN` is equal to itself. Every number is equal to itself. `0` cannot be negative."

- Division by zero gives `Inf`, `-Inf` or `NaN`; it does not fail.
- Overflow produces `Inf`.
- `0.0 / 0.0` is NaN, > "A value, not a failure".
- Ordering: `not (Nan < 1.0)`.
- [API] `<=` is special-cased so that `NaN <= NaN` succeeds, while `<` and `>` fail on any NaN operand. `-0.0` exists as a bit pattern but is equal to `0.0`, and > "division normalises a negative-zero divisor to positive zero". Source: https://verselang.github.io/book/api/verse_runtime_api.html (`float` section)

### 4.3 `rational`
Source: https://verselang.github.io/book/02_primitives/#rationals

```verse
X := 7 / 3    # X has type rational, representing exactly 7÷3
(5 / 2) = (10 / 4)      # true
(1 / -3) = (-1 / 3)     # true: negative moves to numerator
(2 / 1) = 2             # true
```

- There is no rational literal. Values are reduced to lowest terms, with the sign on the numerator.
- > "*`int` is a subtype of `rational`*".
- You cannot overload on `int` versus `rational`.
- Arithmetic on rationals (`+ - * /`, `<`) is UNSPECIFIED in book. The operator tables list only `int` and `float`; [API] mentions only that the `+` instruction "is shared with… rational addition".

### 4.4 `logic`
Source: https://verselang.github.io/book/02_primitives/#booleans

> "The `logic` type only supports query operations and comparison operations."

`logic{e}` converts success to `true` and failure to `false`. It requires that `e` > "at least a superficial possibility of failure": `logic{0}` is an error, `logic{false?}` is fine (https://verselang.github.io/book/01_expressions/#boolean-literals).

### 4.5 `char`, `char32`, `string`
See §1.5–1.6.
- `string` is `[]char`. Strings index with failure and are mutable through `var`, e.g. `set S[0] = 'F'` (https://verselang.github.io/book/02_primitives/#characters-and-strings).
- Equality > "is done by code point, and is case sensitive". There is no Unicode normalization.

### 4.6 Option `?t`
Source: https://verselang.github.io/book/03_containers/#optionals

```verse
A:?int = option{42}
var B:?int = false     # this optional has no element
A? + 2 = 44
MaybeAFloat := option{GetAFloatOrFail[]}
```

> "The two are inverses: `?` turns an optional into a `<decides>` expression, and `option{...}` turns a `<decides>` expression into an optional."

Options nest (`??int`). `MaybeEntity?.Name` is the safe-navigation form (https://verselang.github.io/book/08_failure/#chained-access).

### 4.7 Tuples
Sources: https://verselang.github.io/book/03_containers/#tuple and https://verselang.github.io/book/01_expressions/#tuples

```verse
Point := (10, 20)
Point(0) = 10
Pair:tuple(int,int) = (10, 20)
Describe(MyTuple) = "1 two"   # expands to Describe(1, "two")
```

- > "tuple indexing cannot fail: any attempt to use an out-of-bounds index results in a compile-time error."
- > "there is currently no syntax to construct a single-element tuple value."
- Tuples auto-expand into argument lists and convert to arrays, but only in one direction.

### 4.8 Arrays `[]t` and maps `[k]v`
See §9.

### 4.9 `any`, `comparable`, `type`
Sources: https://verselang.github.io/book/02_primitives/#any, https://verselang.github.io/book/11_types/#type-any and https://verselang.github.io/book/11_types/#comparable-and-equality

- `any` is the top type. It > "supports very few operations". Joins of unrelated types become `any`, e.g. `if (UseNumber?) then 42 else "text"`.
- `comparable` is the class of types that support `=` and `<>`:
  - `int`, `float`, `rational`, `logic`, `char`, `char32`, `string`;
  - enums;
  - `<unique>` classes (identity equality);
  - arrays, maps, tuples and options of comparable types;
  - structs whose fields are all comparable.
- Plain classes, functions and `any` are not comparable.
- `type` is a metatype, used in `where t:type`.

### 4.10 `void`, `true`, `false`, `tuple()`
Sources: https://verselang.github.io/book/02_primitives/#void-true-tuple-and-false and https://verselang.github.io/book/11_types/#type-void

```verse
Nothing:void    = false
Unit:tuple()    = false
Flag:true       = false
Empty:[]int = false
F():void = 1             # Valid - returns int, typed as void
```

- > "Verse has a single 'there is nothing interesting here' value. It can be written `false` or `()`, and the types `void`, `true` and `tuple()` all describe it."
- `void` > "accepts any value"; any value converts to it.
- `true <: logic`.
- As a *type*, `false` is > "the empty type that contains no values at all" (https://verselang.github.io/book/11_types/). It is the bottom type, the type of `break` and `return`.
- **CONFLICT / care:** the token `false` is a `logic` value, the empty option, the empty array or map, and the unit value. It is also the name of the bottom type. An implementation has to resolve it by context.

### 4.11 Subtyping summary
Sources: https://verselang.github.io/book/11_types/#understanding-subtyping, https://verselang.github.io/book/11_types/#void-and-false and https://verselang.github.io/book/06_functions/#types-variance-and-effects

- `int <: rational`.
- The numeric types are otherwise siblings: > "The numeric types (`int`, `float`, `rational`)… are siblings rather than ancestors and descendants."
- Arrays, options and tuples are covariant. Maps are covariant in both key and value.
- Functions are contravariant in parameters and covariant in results. Fewer effects make a subtype.
- Classes and interfaces use nominal subtyping.
- Tuples convert to arrays when every element fits the element type.
- Types with a `var` field of type `t` are invariant in `t` (https://verselang.github.io/book/06_functions/#polarity-and-variance).
- There is no implicit `int`→`float` conversion; write `X * 1.0` (https://verselang.github.io/book/11_types/#numeric-and-string-conversions).
- Refinement types exist, e.g. `type{_X:int where 0 <= _X, _X <= 120}`, and are checked with casts such as `age[150]` (https://verselang.github.io/book/11_types/#refinement-types).

---

## 5. Operators

### 5.1 Precedence table
Source: https://verselang.github.io/book/04_operators/#precedence

| Prec | Operators | Assoc. |
|---|---|---|
| 11 | `.` `[]` `()` `{}` postfix `?` | Left |
| 10 | unary `+` `-`, `not` | Right |
| 9 | `*` `/` | Left |
| 8 | binary `+` `-` | Left |
| 7 | `=` `<>` `<` `<=` `>` `>=` | Right (per table) |
| 5 | `and` | Left |
| 4 | `or` | Left |
| 3 | `..` | Left |
| 2 | lambdas | "(not yet supported)" |
| 1 | `:=`, `set =` | Right |

- **CONFLICT on associativity of the relational operators.**
  - The table says "Right".
  - The Expressions chapter says > "All comparison operators have the same precedence and evaluate left-to-right" (https://verselang.github.io/book/01_expressions/#comparison-operations).
  - Chains are declared to be special syntax (§5.4).
  - [VC] says > "comparison is right-associative". With the return-left-operand rule, right association gives exactly the chain semantics: check every adjacent pair, return the leftmost operand.
- The operators page says `A = B` > "tests equality and returns a logic value". That contradicts §5.4. Treat it as a doc error.

### 5.2 Arithmetic
Sources: https://verselang.github.io/book/04_operators/#basic-arithmetic and https://verselang.github.io/book/04_operators/#type-conversions

```verse
9 / 3 = 3         # a rational compares equal to an int
Floor(10 / 3) = 3
not (10 / 0 = 0)  # division by zero fails rather than erroring
5 * 2.0 = 10.0
# 5 + 2.0  # Error: no operator'+' overload takes (int, float)
```

- `+` also concatenates strings and arrays.
- Only `*` mixes `int` with `float`, and the result is a `float`.

### 5.3 Integer division and the rounding functions
Sources: https://verselang.github.io/book/02_primitives/#rationals, https://verselang.github.io/book/01_expressions/#arithmetic-operations and https://verselang.github.io/book/api/verse_runtime_api.html (sections `int`, `rational`, `Math`)

- > "For integers, the operator `/` is failable, and the result is a `rational` type if it succeeds."
- > "dividing two integers yields a `rational`, not an `int`, so the quotient cannot be assigned to an `int` variable".
- [API] signature: `operator'/'(Lhs:int, Rhs:int)<converges><decides><predicts>:rational`. > "To land back on an `int`, say which you meant: `Floor[X / Y]`, `Ceil[X / Y]`, or `Quotient[X, Y]`."

| Function | Fails? | Semantics |
|---|---|---|
| `Floor(rational)`, `Ceil(rational)` | no | > "On a rational argument neither function can fail". Floor rounds toward −∞, Ceil toward +∞: `Floor((-5) / 2) = -3`. |
| `Floor[f]`, `Ceil[f]`, `Round[f]`, `Int[f]` (float→int) | yes, `<decides>` | Fail for NaN and ±Inf. `Round` is ties-to-even (`Round[2.5] = 2`). `Int` truncates toward zero. [API] A result outside the 64-bit range "raises an integer-bounds error that *halts the content scope*". |
| `Quotient[X, Y]` | yes, `<decides>` | [API] `Quotient<native><public>(X:int, Y:int)<computes><predicts><decides>:int`. > "Euclidean division… `Quotient[-7, 2]` is `-4`". Fails when `Y = 0`. `MinInt / -1` is an unrecoverable runtime error. |
| `Mod[X, Y]` | yes, `<decides>` | [API] > "the result always lies in `[0, Abs(Y))`, never negative. `Mod[-7, 2]` is `1`". Fails when `Y = 0`. |
| `BitShiftLeft[V,N]`, `BitShiftRight[V,N]` | yes | Fail when the count is negative. Shifts are arithmetic. |
| `BitAnd/BitOr/BitXor/BitNot` | no | Two's complement of unbounded width (https://verselang.github.io/book/04_operators/#bitwise-operations). |

The book writes both `Floor(10 / 3)` and `Floor[X / Y]`. The rational overload is not `<decides>`; the division inside it is. So a failure context is needed in both forms.

### 5.4 Comparisons are failable and return their left operand
Sources: https://verselang.github.io/book/01_expressions/#comparison-operations and https://verselang.github.io/book/08_failure/#expressions-in-decides

```verse
Left := 0 < 10
Left = 0                  # A comparison returns its left operand
0 <= Value <= 100         # Chain checks BOTH 0 <= Value and Value <= 100
GetIfNotEqual(X:int, Y:int)<decides>:int =
    X <> Y  # Returns X when X ≠ Y, fails when X = Y
```

- > "comparison operators return their left operand when the comparison succeeds".
- Chains: > "it is special syntax that checks both `A <= B` **and** `B <= C`, while returning the leftmost operand (`A`) on success."
- [API] signature: `operator'='(Lhs:t, Rhs:comparable where t:subtype(comparable))<converges><decides><predicts>:t`. > "Equality here is *extensional*".
- The Types chapter instead says the result type is > "the least upper bound of their types" (https://verselang.github.io/book/11_types/#comparable-and-equality). This is a minor CONFLICT with the API's `:t`.
- `<`, `<=`, `>`, `>=` are defined on `int` and `float` (table at https://verselang.github.io/book/04_operators/#relational-operators). Ordering on rationals and strings is UNSPECIFIED in book.
- Mixed-type equality type-checks but always fails: > "Comparisons between different types still compile, but they always fail: `not (0 = 0.0)`".
- An option never equals a bare value: `not (Opt = Regular)` (https://verselang.github.io/book/08_failure/#comparison).
- Arrays compare equal to tuples structurally: `array{1, 2, 3} = (1, 2, 3)`.
- Map equality is order-sensitive (§9).

### 5.5 `and`, `or`, `not`
Sources: https://verselang.github.io/book/04_operators/#truth-table, https://verselang.github.io/book/01_expressions/#logical-operations and https://verselang.github.io/book/04_operators/#not-operator

| P | Q | `P and Q` | `P or Q` | `not P` |
|---|---|---|---|---|
| S | S | Succeeds (Q's value) | Succeeds (P's value) | Fails |
| S | F | Fails | Succeeds (P's value) | Fails |
| F | S | Fails | Succeeds (Q's value) | Succeeds |
| F | F | Fails | Fails | Succeeds |

- Both operators short-circuit. `and` binds tighter than `or`.
- The value produced by a successful `not P` is UNSPECIFIED in book. Presumably it is the unit value.
- `or` gives a fallback: `Value := MaybeValue? or 42`. With disjoint operand types the result is `any` (https://verselang.github.io/book/11_types/#type-any).
- An `or` whose right operand cannot fail makes the whole expression non-failing. The book uses this as a way to "Handle with or" in a function without `<decides>` (https://verselang.github.io/book/08_failure/#idioms-and-patterns).
- The left operand of `or` and the operand of `not` each get a new lexical scope (https://verselang.github.io/book/07_control/#defer-statements).
- `not` rolls back effects:

  ```verse
  var X:int = 0
  if (not (set X = 5, IsGameOver?)):
      X = 0  # the assignment was undone when IsGameOver? failed
  ```

  > "`not not Exp` -- it succeeds if `Exp` succeeds but all effects of `Exp` are thrown away." (https://verselang.github.io/book/08_failure/#the-logic-of-failure)

- Whether effects of a *failed* left operand of `or` are rolled back is not stated for `or` specifically. It follows from the general rule in §6.3 but is not explicitly stated.

---

## 6. Failure

### 6.1 Failable expressions
Source: https://verselang.github.io/book/08_failure/#failable-expressions

- > "Failure is neither an error nor an exception. A failing expression does not crash the program and raises nothing to be caught. It simply produces no value".
- Failable expressions include:
  - array indexing, map lookup and string indexing;
  - comparisons;
  - `int` `/`;
  - `?`;
  - calls to `<decides>` functions;
  - casts `T[v]` on `<castable>` classes (https://verselang.github.io/book/08_failure/#casts-as-decides);
  - refinement casts;
  - `first`;
  - a `case` without a match inside a `<decides>` context.
- **CONFLICT on what `?` accepts.** The failure chapter says > "The query operator `?` turns any value into a failable expression. When applied to `false`, it always fails. When applied to any other value, it succeeds with that value." [API] defines `?` only on `logic` and `?t`, and the operators chapter describes it as > "checks if a `logic` value is `true`". Implement the typed version.
- `false?` always fails. The idiom `{false?; 0.0}` fails a branch (https://verselang.github.io/book/00_overview/#an-example).

### 6.2 Failure contexts
Sources: https://verselang.github.io/book/08_failure/#failure-contexts, https://verselang.github.io/book/07_control/#if-expressions and https://verselang.github.io/book/13_effects/#effect-composition

> "They can only appear in failure contexts--places where the language knows how to handle both success and failure."

The book lists or shows these contexts:

- the condition of `if`;
- each iteration of a `for` or `first` domain;
- the body of a `<decides>` function;
- `logic{}` and `option{}`;
- the operand of `not`;
- the left operand of `or`.

The `if` condition > "must contain at least one expression that can fail". `if (1 + 1)` is an error.

`F[args]` is not a context. It is the call syntax required for `<decides>` callees: > "The square bracket syntax `Func[]` is **required** for calling functions that may fail… Use regular parentheses `Func()` for functions that always succeed" (https://verselang.github.io/book/01_expressions/#computed-access). Failable calls outside a context are compile errors: `Player := FindPlayer[Name]  # ERROR: Unhandled failure` (https://verselang.github.io/book/08_failure/#idioms-and-patterns).

### 6.3 Speculative execution and rollback
Sources: https://verselang.github.io/book/08_failure/#speculative-execution and https://verselang.github.io/book/07_control/#if-expressions

```verse
TryScore(Score:int)<transacts>:logic =
    if:
        set Attempts += 1  # Provisional change
        Score > 100        # Might fail
    then:
        true
    else:
        false
not TryScore(50)?   # Condition failed
Attempts = 1        # The increment was rolled back - undone!
```

- > "When you execute code in a failure context, changes to mutable variables are provisional—they only become permanent if the entire context succeeds."
- > "Either everything succeeds and all changes are committed, or something fails and nothing changes."
- Rollback spans calls: if a final check fails, > "every change any of those methods performed is rolled back with it".
- The `if (not F[])` trap: when `F[]` succeeds, `not` fails, so the `if` condition fails and `F`'s effects are rolled back. The safe pattern is `Succeeded := logic{F[]}` bound before the `if` (https://verselang.github.io/book/07_control/#handling-only-failures).
- `defer` does not run on failure: > "failure triggers a rollback that undoes all effects, including the scheduling of defer blocks" (https://verselang.github.io/book/07_control/#defer-statements).
- Rollback also covers:
  - `weak_map` updates (https://verselang.github.io/book/03_containers/#transaction-and-rollback-semantics);
  - event `Subscribe` and `Cancel`;
  - frozen time, since `GetSecondsSinceEpoch()` is constant within a transaction (https://verselang.github.io/book/14_concurrency/#time-is-frozen-within-a-transaction).
- Runtime errors are not failures: > "*runtime errors* represent unrecoverable conditions that terminate execution… cannot be caught or recovered within Verse code" (`Err()`, BPVM overflow) (https://verselang.github.io/book/08_failure/#runtime-errors).
- Nested speculation (an inner commit inside an outer rollback) is not spelled out. The rule "permanent if the entire context succeeds" implies that an outer failure discards inner commits.

### 6.4 `<decides>`
Sources: https://verselang.github.io/book/13_effects/#cardinality-effects and https://verselang.github.io/book/08_failure/#failure-contexts

```verse
ValidateAge(Age:int)<decides>:int =
    Age >= 0    # Fails if age is negative
    Age <= 150  # Fails if age is unrealistic
    Age         # Returns the age if both checks pass
```

- > "Functions marked with `<decides>` create a failure context for their entire body".
- `<decides>` cannot be combined with `<suspends>`.
- A function without `<decides>` is a subtype of the same function with it, so `F1:type{_(:int)<computes><decides>:int} = PureAdd` and `F1[5] = 6` are valid.

### 6.5 `<transacts>` and rollback permission
Source: https://verselang.github.io/book/08_failure/#speculative-execution

> "Functions that modify state in failure contexts must use the `<transacts>` or the `<writes>` effect specifier".

`<transacts>` = `{reads, writes, allocates}` and is the default (§8.4).

### 6.6 `?` query, `option{}`, `logic{}`
Sources: https://verselang.github.io/book/03_containers/#optionals, https://verselang.github.io/book/08_failure/#option-types and https://verselang.github.io/book/02_primitives/#booleans

- `X?` on `?t` yields the contents or fails. On `logic` it succeeds when the value is `true`.
- `option{e}` gives `option{v}` on success and `false` on failure.
- `logic{e}` gives `true` or `false`.
- > "Unwrapping is only allowed in failure contexts".

### 6.7 `case` and failure
Source: https://verselang.github.io/book/07_control/#case-expressions

> "Incomplete case coverage is allowed in a `<decides>` context". An unmatched value makes the function fail.

### 6.8 Failure versus `<suspends>`
Source: https://verselang.github.io/book/13_effects/#suspension-effects

A `<suspends>` function may call a `<decides>` function only inside a local failure context such as `if (ValidateInput[Value])`.

### 6.9 How [VC] maps failure and choice to the surface (informative only)
Source: https://www.cs.tufts.edu/~nr/cs257/archive/simon-peyton-jones/verse-icfp23.pdf, §2.2, §2.5, §2.8, §6.7, Appendix F

- **Failure.** VC's `fail` "yields no values". The surface language's "fails and produces nothing" corresponds to zero results.
- **Choice.** `e1 | e2` yields all values of e1 then all values of e2, in order. The bar glyph is lost in the PDF text extraction. The book never exposes `|`. Surface analogues are `or` (taking the first success) and the iteration of `for` domains.
- **`if`.** `if (∃x. e1) then e2 else e3` desugars to `(one{(∃x. e1; λ⟨⟩. e2) | (λ⟨⟩. e3)})⟨⟩`.
- **`one{e}`.** > "if e fails, one{e} fails; otherwise one{e} returns the first of the values yielded by e". The condition variables of `if` are "rigid" from outside.
- **`for`.** `for(e1) do e2` desugars to `v := all{e1; λ⟨⟩. e2}; map⟨λz. z⟨⟩, v⟩`. `all{fail}` is `⟨⟩`, an empty array. Filters "fall out naturally by just using a possibly failing expression in e1". > "In Verse, a = for{e} does the job; in VC, a = all{e}".
- **Comparisons.** `gt⟨k1,k2⟩` returns `k1` when k1 > k2 and fails otherwise. This matches §5.4.
- **`=`.** `e1 = e2` desugars to `x := e1; x = e2; x`, which returns the value.
- **Store (Appendix F).** > "if a computation fails, then any updates will not be visible outside the construct that handles the failures". For `for`: > "If any iteration of d fails, then the effects of that computation are not visible outside d". Effects of earlier successful iterations are visible to later ones.
- **Caveat.** VC's `=` is unification over logical variables. The book exposes no logical variables. Surface `=` on ground values behaves as an equality test.

---

## 7. Control flow

### 7.1 `if`
Sources: https://verselang.github.io/book/07_control/#if-expressions and https://verselang.github.io/book/01_expressions/#conditional

```verse
if (Action = "jump", Player.CanJump[]):
    Player.Jump()
else if (Action = "attack", Weapon := Player.GetEquippedWeapon[]):
    Weapon.Fire()
else:
    Player.Idle()
if:
    Value > 0
    Value < 100
then:
    "Valid"
else:
    "Out of range"
```

- Conditions are separated by commas or newlines. All must succeed, left to right, and later conditions can use earlier bindings.
- Branches with incompatible types widen to `any`.
- > "All branches must produce a value for the `if` to be used as an expression."
- > "The else clause can be omitted, though this affects the type of the expression." The resulting type is UNSPECIFIED in book.

### 7.2 `for`
Source: https://verselang.github.io/book/07_control/#for-expressions

```verse
Doubled := for (Item : Collection) { Item * 2 }
for (Index -> Item : Collection) { ... }          # arrays: int index; maps: key
Squares := for (I := 1..Count - 1) { I * I }      # ranges bind with :=
SafeDivision := for (X := -3..3, X <> 0, Y := Floor[10.0 / (X*1.0)]):
    Y  # Skips X=0
Cells := for (X := 1..3, Y := 1..3):
    X*10 + Y
Cells = array{11, 12, 13, 21, 22, 23, 31, 32, 33}
Result := for:
      V : Values
      V >= 10.0
      R := Floor[V]
   do:
      R*2.0
```

**What `for` produces**

- > "A for expression evaluates to an array". > "When any expression in the iteration header fails, that iteration is skipped."
- Several generators give > "the cartesian product", with the leftmost generator outermost.
- A `for` with no generator runs its body at most once and yields a 0- or 1-element array: `for(Some?) { 1 } = array{1}`.
- Failable bindings may precede a generator and feed it.

**Generators and ranges**

- Sources are > "Only ranges (`1..10`), arrays, maps, and strings".
- Ranges are inclusive at both ends. `for (N := 5..1) { N } = array{}`. They are `int`-only and are not first-class values: > "ranges are only supported as the iterated expression of `for`, `sync`, `rush`, or `race`".
- Maps iterate in insertion order. `for (V : M)` yields values, and `for (K -> V : M)` yields pairs.
- `;` and `,` both separate clauses but cannot be mixed.

**Restrictions**

- No `var` in clauses.
- The iteration variable cannot be redefined.
- Filters must be failable.
- `break` cannot exit a `for`.
- There is no `continue`.

**Unstated**

- What happens if the *body* fails, inside a `<decides>` context, is UNSPECIFIED in book. In [VC]'s desugaring a failing body would make the whole `for` fail.
- The type of `for` whose body is `void` is not stated, e.g. `for (V : Values). DoSomething(V)`. Presumably `[]void` or similar: UNSPECIFIED in book.

### 7.3 `first`
Source: https://verselang.github.io/book/07_control/#first-expressions

```verse
first (Player : Players; GetScore[Player] > Threshold):
    Player
```

`first` has the same domain syntax as `for`. It yields the body value of the first successful iteration. > "If no iteration reaches the body, `first` fails, so it requires a `<decides>` context."

### 7.4 `loop` and `break`
Sources: https://verselang.github.io/book/07_control/#loop-expressions and https://verselang.github.io/book/01_expressions/#loop

```verse
loop:
    set B = if (B > X) { break } else { 2*B }
    set C = C+1
```

- > "A loop expression produces a value of type `true`".
- `break` has bottom type and exits the innermost `loop` only.
- > "The `break` statement must appear in a code block, not as part of a complex expression. A loop must contain at least one non-break statement."
- The example above does put `break` inside an `if` used as a value. The book permits this but does not pin down exactly where `break` may appear.

### 7.5 `return`
Source: https://verselang.github.io/book/07_control/#return-statements

```verse
ValidateInput(Value:int):string =
    if (Value < 0):
        return "Error: Negative value"
    "Valid"     # Implicit return
```

- > "They must be in 'tail position,' meaning they must be the last operation performed before control exits a scope."
- `return` without a value has bottom type (https://verselang.github.io/book/06_functions/#restrictions_1).
- `return` from inside a `for` body is used in examples (`return option{I}`).
- What `return` inside a failing `<decides>` region does is UNSPECIFIED in book.

### 7.6 `case`
Sources: https://verselang.github.io/book/07_control/#case-expressions and https://verselang.github.io/book/09_structs_enums/#exhaustiveness

```verse
case(WeaponType):
    "sword"  => 50.0
    _        => 10.0
```

- Scrutinee types: > "**Primitives**: `int`, `logic`, `char`… **Strings**… **Enums**… **Refinement types**". `case` does not work on `float`, objects or tuples.
- Patterns are values or `_`. Destructuring and guards are not documented: UNSPECIFIED in book.
- Exhaustiveness:
  - A closed enum with full coverage needs no `_`; adding one is a warning.
  - Partial coverage without `_` is allowed only in `<decides>`, where unmatched values fail.
  - Open enums always need `_` or `<decides>`.
  - Duplicate cases and cases after `_` are errors.

### 7.7 `defer` (not in your list; relevant to rollback)
Source: https://verselang.github.io/book/07_control/#defer-statements

- `defer` runs when its scope exits, in LIFO order.
- It does not run when the scope fails.
- It cannot fail, suspend, `return` or `break`.

### 7.8 [VC] cross-reference
`if` is `one`, and `for` is `all` + `map` (§6.9).

---

## 8. Functions

### 8.1 Definition and calling
Sources: https://verselang.github.io/book/06_functions/#parameters and https://verselang.github.io/book/08_failure/#idioms-and-patterns

```verse
ProcessData(Name:string, Age:int, Score:float):string =
    "{Name} is {Age} years old with a score of {Score}"
GetValue()<transacts><decides>:int = 42
if (X := GetValue[]):     # [] is required: GetValue can fail
Y := GetData()            # () is required: GetData always succeeds
```

- The general form is `Name(Params)<effects>:ReturnType = Body`. The body is a block whose value is the result.
- An omitted return type, `F2<public>(X:int) := X + 1`, is a future "transparent function" (https://verselang.github.io/book/06_functions/#publishing-functions).
- `void` return discards the body value.

### 8.2 Named and default parameters
Source: https://verselang.github.io/book/06_functions/#named-parameters

```verse
Log(Message:string, ?Level:int=1, ?Color:string="white"):string = ...
Log("Error", ?Color := "red", ?Level := 3)
```

- > "After the first named parameter, all subsequent parameters must also be named."
- Positional arguments come first.
- Defaults are evaluated in the defining scope and can reference earlier parameters.
- Default values are not part of function types.

### 8.3 Tuples as arguments
Source: https://verselang.github.io/book/06_functions/#flattening-and-unflattening

- Tuples flatten into multiple parameters and unflatten into a single tuple parameter.
- `F(P:tuple(int,int))` and `F(X:int, Y:int)` cannot both be defined.
- Destructuring parameters are allowed: `Func(A:int, (B:int, C:int), D:int)`.

### 8.4 Effect specifiers
Sources: https://verselang.github.io/book/13_effects/#effect-families-and-specifiers and https://verselang.github.io/book/13_effects/#how-effects-compose

| Specifier | Implies | Notes (quoted from the table) |
|---|---|---|
| `<computes>` | `{}` (heap) | "Exclusive; Pure computation" |
| `<reads>` | `{reads}` | "Allows reading mutable states" |
| `<writes>` | `{writes}` | "Allows writing mutable states" |
| `<allocates>` | `{allocates}` | "Allows allocation of mutable memory" |
| `<transacts>` | `{reads, writes, allocates}` | "Exclusive; default" |
| `<decides>` | `{succeeds, fails}` | "Cannot combine with `<suspends>`" |
| `<suspends>` | `{suspends}` | "Cannot combine with `<decides>`" |
| `<converges>` | `{}` (divergence) | "Exclusive; Native functions, abstract methods, type signatures" |
| `<predicts>` | clears `dictates` | "not yet released" |
| `<varies>` | — | **UNSPECIFIED in book.** It appears nowhere in the chapters or in the generated API reference. Epic's separate page https://dev.epicgames.com/documentation/en-us/uefn/specifiers-and-attributes-in-verse may cover it; that page is not verified here. |

- Exclusive specifiers are `<converges>`, `<computes>` and `<transacts>`; at most one is allowed. Additive specifiers are `<suspends>`, `<decides>`, `<reads>`, `<writes>` and `<allocates>`.
- Writing a specifier replaces its whole family: > "Specifying `<reads>` clears the `writes` and `allocates` bits".
- Default effects: > "it has effects `dictates`, `reads`, `writes`, `allocates` and `succeeds`".
- Effects must propagate up the call chain, except where hidden:
  - `if` conditions hide `fails`;
  - `spawn` hides `suspends`;
  - `option{}` converts `fails` into a value.
- Subtyping: `<computes>` <: `<reads>` <: `<transacts>`, and no-`<decides>` <: `<decides>`. Effects join across branches.
- Data types can carry `<computes>`, `<transacts>` and similar, which constrain their constructors. They cannot carry `<decides>` or `<suspends>` (https://verselang.github.io/book/13_effects/#effects-on-data-types).

### 8.5 Overloading
Sources: https://verselang.github.io/book/06_functions/#overloading_1 and https://verselang.github.io/book/06_functions/#types

- Overloads must have distinct parameter types: there must be no value that matches both. Effects alone do not make overloads distinct.
- Pairs that are not distinct:
  - `int`/`rational`;
  - `?t`/`logic`;
  - `[]t`/`[k]v`;
  - functions/maps/arrays;
  - class/interface;
  - subclass pairs;
  - `void` with anything;
  - `tuple()`/`[]t`;
  - `tuple(int)`/`?int`.
- An overloaded name cannot be captured as a value (`g := f` is an error).

### 8.6 Recursion
The book has no dedicated section on recursion.
- Methods recurse in examples, e.g. `Tmp.Equals[OtherNext]` inside `Equals` (https://verselang.github.io/book/05_mutability/#the-pure-foundation).
- Nested functions > "can be recursive", but > "mutually recursive nested functions are not allowed" (https://verselang.github.io/book/06_functions/#nested-functions).
- Top-level mutual recursion and divergence rules are UNSPECIFIED in book. There is no `<converges>` for user code: "Currently in planning".

### 8.7 Functions as values
Sources: https://verselang.github.io/book/06_functions/#lambdas and https://verselang.github.io/book/06_functions/#using-type

- Function types are written `type{_(:int, :string)<decides>:float}`, or `int->string`.
- > "Lambda expressions with the `=>` operator are not supported".
- Closures come from nested functions, which are themselves marked > "Unreleased Feature".
- Intrinsics and extension methods cannot be referenced as values.

---

## 9. Arrays, tuples and maps

### 9.1 Arrays
Sources: https://verselang.github.io/book/03_containers/#arrays and https://verselang.github.io/book/05_mutability/#basic-array-mutation

```verse
B : []int = array{1, 2, 3}
B[0]                     # succeeds with 1; B[10] fails
var C:[]int= B + array{4}
set C += array{5}
set Values += (7, 8, 9)  # tuple auto-converted
not (set A[1] = 1)       # Fails - index out of bounds
```

- Arrays are immutable values. `var` rebinding gives the appearance of mutation.
- `A[i]` is `<decides>`.
- [API] `set A[i] = v` > "fails when the index is out of range, so the whole assignment is a failable expression".
- `.Length` gives the length; `+` concatenates.
- Element type is the join of the elements' types. An empty `array{}` needs an annotation.
- Methods:
  - failable: `Slice[a,b]`, `Find[x]`, `RemoveFirstElement[x]`, `Remove[a,b]`, `ReplaceFirstElement[x,y]`, `ReplaceElement[i,x]`, `Insert[i,arr]`, `Last[n]`;
  - total: `RemoveAllElements(x)`, `ReplaceAllElements(x,y)`, `ReplaceAll(pat,rep)`, `Concatenate(...)`.

  Source: https://verselang.github.io/book/03_containers/#array-methods
- Indexing with an index out of range: > "There is no unchecked variant" ([API]).

### 9.2 Tuples
See §4.7. Tuples cannot be mutated element-wise.

### 9.3 Maps
Sources: https://verselang.github.io/book/03_containers/#maps and https://verselang.github.io/book/05_mutability/#basic-map-mutation

```verse
var Friendliness:[string]int = map{"peach" => 1000}
set Friendliness["pelican"] = 17          # succeeds: adds a new key
set Friendliness["peach"] += 2000         # succeeds: updates an existing key
not (set Friendliness["tomato"] += 1000)  # fails: "tomato" is not a key
not Weights["car"]                        # lookup fails on a missing key
```

- `M[k]` is `<decides>`.
- `set M[k] = v` inserts or updates. `set M[k] op= v` fails if the key is missing. [API] > "That asymmetry between `=` and `+=` on maps surprises nearly everyone once."
- Insertion order is preserved for iteration and for equality: > "Two maps are equal only if they contain the same key–value pairs **in the same order**". Updating a key keeps its position, and new keys go at the end.
- In a literal with duplicate keys, the last value wins and takes the position of the *last* occurrence.
- `.Length`, `ConcatenateMaps(A, B)` (right side wins). There is no delete; rebuild the map instead.
- Key types must be comparable. **CONFLICT on arrays and maps as keys:**
  - The Containers chapter says the compiler rejects array and map keys, quoting "Use of `[]int` as a map key is not yet implemented". `string` is the exception.
  - The Types chapter lists > "Arrays of comparable types" and "Maps with comparable keys and values" as valid key types (https://verselang.github.io/book/11_types/#map-keys-and-comparable).
  - The Containers wording is more specific.
- Failable keys in map literals are not implemented: `map{1/2 => ...}` is disallowed; bind the key first.
- Nested `set` fails if any intermediate key or index is missing: `not (set Grid["oranges"][0] = 10)`.
- `weak_map(k,v)` has no `Length` and no iteration. It is out of v1 scope.

---

## 10. Structs, enums, classes and interfaces (brief)

- **Structs** (https://verselang.github.io/book/09_structs_enums/#structs):
  - Example: `vector2 := struct: X : float = 0.0`; construct with `vector2{X := 1.0}`.
  - > "All struct fields are public and immutable by default. Structs cannot have methods, constructors, or participate in inheritance hierarchies."
  - Value semantics; equality is field by field when all fields are comparable.
  - Parametric: `wrapper(t:type) := struct: Value : t`.
  - Field mutation through `var` requires `struct<computes>` (§3.3).
  - Object construction forms (https://verselang.github.io/book/04_operators/#object-construction):

    ```verse
    point{X := 10, Y := 20}
    point{X := 10; Y := 20}
    point:
        X := 10
        Y := 20
    point . X := 10
    ```

    In the braces-and-newlines form a trailing comma is an error.
- **Enums** (https://verselang.github.io/book/09_structs_enums/#enums):
  - Example: `game_state := enum: MainMenu ...`, or `enum{A, B}`.
  - Values are written `game_state.MainMenu`.
  - Enums must be defined at module or class level, not inside a function or expression.
  - `<closed>` is the default; `<open>` also exists. See §7.6 for exhaustiveness.
  - Enums are comparable and usable as map keys. Values of different enum types are always unequal, and comparing them still compiles.
  - No ordering or integer conversion is documented: UNSPECIFIED in book.
- **Classes** (https://verselang.github.io/book/10_classes_interfaces/):
  - Module scope only; single inheritance via `class(parent)`.
  - Reference semantics. Only `var` fields are mutable.
  - Not comparable unless `<unique>`, which gives identity equality.
  - Specifiers include `<abstract>`, `<final>`, `<castable>` (enables `T[x]` casts), `<concrete>` and `<persistable>`.
  - Methods with `<override>`, `(super:)`, constructor functions `F<constructor>(...) := cls{...}`, and `block:` initializers.
- **Interfaces:** `i := interface: ...`. A class may implement several. They can provide default method bodies and fields.

---

## 11. Concurrency (excluded from v1)
Source: https://verselang.github.io/book/14_concurrency/

- All structured forms require `<suspends>`, and `<suspends>` is viral.
- `sync:` runs its arms together and waits for all of them, giving a tuple of results in source order.
- `race:` returns the first arm to finish and cancels the rest.
- `rush:` returns the first arm to finish without cancelling the rest.
- `branch:` is fire-and-forget, cancelled when the enclosing function scope exits.
- `spawn{e}` works in any context. Its body must be `<suspends>` and not `<decides>`. It returns a `task(t)` and outlives its creator.
- `rush` and `branch` cannot appear directly in a `loop` or `for` body.
- `defer` runs when a task is cancelled.

---

## 12. Marked as subject to change, unreleased or unspecified

**Global**

- > "some features may be discussed before they are officially released and are thus subject to change" (https://verselang.github.io/book/).

**Language features marked unreleased or not supported**

- Lambdas: not supported (https://verselang.github.io/book/06_functions/#lambdas; precedence level 2).
- Nested functions: > "have not yet been released" (https://verselang.github.io/book/06_functions/#nested-functions). They are nonetheless used for closures throughout the book.
- `<predicts>`: > "not yet released". The divergence family and `<converges>` are "Currently in planning" (https://verselang.github.io/book/13_effects/).
- `no_rollback`: "To be deprecated".
- Live variables: > "have not yet been released" (https://verselang.github.io/book/15_live_variables/).
- Transparent functions: "Future version" (https://verselang.github.io/book/06_functions/#publishing-functions).
- No `continue`: > "Verse does not currently support a `continue` statement" (https://verselang.github.io/book/07_control/#for-as-an-expression).
- Map keys: arrays and maps are "not yet implemented" as keys, and failure in map-literal keys is "not implemented" (https://verselang.github.io/book/03_containers/#maps).
- Single-element tuples cannot be constructed. A tuple parameter holding only named parameters must be passed `()`, which the book calls a "known limitation".
- Multiple constraints on one type parameter: "not yet supported" (https://verselang.github.io/book/11_types/#where-clauses).
- Automatic qualification: "Unreleased Feature" (https://verselang.github.io/book/16_modules/).
- `NextTick()`, sticky events and subscribable events: unreleased (https://verselang.github.io/book/14_concurrency/).
- JSON serialization: unreleased (https://verselang.github.io/book/17_persistable/).

**Library behaviour left open**

- VM divergence: VerseVM and BPVM differ on int overflow (§4.1).
- `ToDiagnostic`: > "may vary between VM implementations and is not guaranteed to be stable".
- `ArcSin`/`ArcCos` outside [-1,1]: > "The engine leaves that behaviour unspecified" (https://verselang.github.io/book/02_primitives/#mathematical-functions).
- [API] `ArTanh(±Inf)`: "unresolved".

**UNSPECIFIED items collected from this digest:** offside-rule details; reserved-word list; `#` inside strings; lexing of the most negative literal; type of an `if` without `else`; value of `not P`; body failure in `for`; `for` with a `void` body; rational arithmetic and ordering; string ordering; module-level forward references; top-level mutual recursion; top-level failable expressions; enum ordering; `<varies>`.
