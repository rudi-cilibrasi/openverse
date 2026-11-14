# Rules of the forms of expressions, statements and the library

The rules openverse takes from the Book of Verse for the causes of [the map
of forms](book-test-conformance.md#forms-of-expressions-statements-and-the-library-a-map)
and of [the map of the forms still on the
list](book-test-conformance.md#the-forms-still-on-the-list-a-map), each pinned with the Book's words, its prose and its tests, at the
revision the other notes pin
([`beaa719`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0)):
a chapter is `docs/NN_*.md` and a line, a test `Tests/FILE:LINE`. Each
section says what openverse did before, what it does now, where the rule
lives, and which programs it changes. Where the prose and the tests
disagree, openverse follows the tests, and the section quotes both. No
Epic compiler was run and no Epic source code was read.

## A `.` and what follows it

**The rule.** A `.`, of a member (`O.F`) or of a body (`if (C). E`), and
what follows it are on one line, with no comment between them; spaces may
be (`O. F`), and a comment before the `.` may (`O<#c#>.F`).

**The Book.** The prose is silent. The tests, `Tests/ReserveDotSpace.versetest`:
`O.f` (`:3`) and `O. f` (`:4`) parse, `O.⏎f` (`:5`) and `O.<#comment#>f`
(`:6`) are refused (3100), `O<#comment#>.f` (`:7`) parses; the file's name
says why: a `.` and a space are reserved for the body of a dot form
(`if (1 < 2). set Num = 42`, `:9-66`). No line of the Book's tests or
chapters ends a line of code with a `.`.

**openverse before.** `O.⏎F` and `O.<#c#>F` were `O.F`; a dot form's body
on the next line was refused by the parser, "expected an expression after
'.', on its line".

**openverse now.** The lexer refuses a `.` followed, after spaces and
tabs, by a line break, a comment or the end of the text (`lexAll`,
`Front/Lexer.lean`): "what follows a '.' must be on its line, with no
comment between". Programs: the error test `dot_body_next_line` (a dot
form's body on the next line) gets this message, at the `.`.

## Members in braces

**The rule.** Two members of a class or an interface written in braces on
one line are separated by `,` or `;`.

**The Book.** The tests: `c:=class{x:int block{}}` is refused (3100,
`Tests/Classes/ClassBlockClause.versetest:19`), and so is its indented form,
`c:=class:` and the line `x:int block{}` (`:20`); the members separated
(`class{block{…}}`, `:23`, and the indented ones) are valid. The prose
separates a class's members by new lines or `;` (ch. 1, "Semicolons vs
Commas").

**openverse before.** In braces, a member could follow another with no
separator; the indented form was refused already.

**openverse now.** `parseClassBody` (`Front/Parser.lean`) refuses a member
that follows another on its line with no `,` or `;`: "expected ',', ';', a
new line or '}' after a member".

## A struct's field set

**The rule.** `set` writes a field of a struct only when the struct is
`<computes>`; a path that reaches an object and writes one of the
object's fields reads the structs before the object, and writes none of
theirs.

**The Book.** Ch. 5, "Only <computes> Structs Allow Field Mutation"
(`05_mutability.md:733-735`): "Only structs marked `<computes>` (pure
structs) allow field mutation through a variable". The tests:
`s := struct{M:int=0}` and `var S:s=s{}; set S.M = 1` refused (3509), the
same with `struct<computes>` valid ("Only members of pure structs can be
mutated through a pointer", `Tests/Mutability.versetest` 424-426); `set
S3[0].S2.C0.CM.S0.A = 77` valid, where `struct3` and `struct2`, the structs
before the object `C0`, are not `<computes>` and `struct1`, `struct0`, those
after its `var` field `CM`, are (`:441-447`, with the definitions at
`:95-115`).

**openverse before.** Any struct's field was set through a `var`.

**openverse now.** `elabSetWith` (`Elab/Control.lean`) walks the path's
field steps, and refuses the first field of a source struct that is not
`<computes>` after the path's last object: "set of field 'M' of s: only a
<computes> struct's fields are set". Programs: the tests `structs`,
`generic_structs`, `nested_set`, `set_op_order`, `set_op_order_paths`,
`choice_set_path_more`, `weak_map`, `class_refs_paths`,
`iface_field_set_paths` and `mutation_tooling` declare the structs whose
fields they set `<computes>` (their output the same); the error test
`set_path_not_var` too, so that its subject, a path from a constant, is
what it refuses.

## A type parameter the parameters determine

**The rule.** Every type parameter of a function, or of a method beyond its
class's, is given by the parameters: it occurs, by the Book's variance
(ch. 10, "Instantiation and Identity"), where values go *in*: in a
parameter's type at a covariant place (a parameter's own type, an array's,
an option's, a map's or a tuple's element, a covariant or invariant class
argument), or in the result's at a contravariant place (a function type's
parameter: `G(N:int where t:type):(t->void)`), or it is named in the bound
of one that is (`Up(X:t where t:subtype(u), u:type)`). Not determining: the
result's covariant places (`Make(N:int where t:type):?t`); a function type's
parameter inside a parameter (`Apply(F:t->void where t:type)`); a type
argument of a class or interface that only takes it in, a contravariant one
(`Use(S:sink(t))`, `sink(t) := class{Take(X:t):void}`); and, transitively,
a parameter named only in such places. A class or interface that does not
use its type parameter (bivariant) gives it: the Book is silent, and an
object holds its type arguments, which openverse's casts refine (#243).

**The Book.** The tests (3503), `Tests/ParametricFunctions.versetest`:
refused, `F(() where t:type):?t` (`:338`), `:[]t` (`:341`), `:[t]u` and
`tuple(?t, ?u)` (`:344`, `:347`, two errors each), `F(G(:t):void where
t:type):void` (`:350`), `F(() where t:type):?class1(t)` with `class1`
holding a `Property:t` (`:353`), `F(:class1(t) where t:type)` with `class1`
taking `t` in its `Method(:t)` only (`:356`, `:361`, `:366`), `F(() where
t:type):void` (`:371`), `F(:u where t:type, u:type)` (`:374`),
`Foo(X:int where t:subtype(u), u:type):?t` (`:586`, two); valid, `G(()
where t:type):(t->void) = F` (`:376-378`), `F(X:[t]u where …):[t]u`
(`:380`), `Foo(:castable_subtype(t) where t:type)` (`:583`), `Foo(X:t
where t:subtype(u), u:type):t` (`:589`). The prose is silent; ch. 2 gives a
type no parameter determines as an argument, `MaybeValueExplicit(t:type,
Value:t, Valid:logic):?t` (`02_primitives.md:1040-1069`).

What looked like a split by VM is not one: `MakeClosure(Callback:
tuple(payload, context)->void, Context: context where payload: type,
context: type):(payload->void)` (`Bugs/FORT-592189-MaybeCoerceToTypeCrash.versetest:44`,
`verse_vm_only`, valid) names `payload` in its result's function type's
parameter, which determines it as `:376` has it; its `bp_vm_only` twin
(`:4`) is an IR error (3502), not this rule's.

**openverse before.** A type parameter without a bound was not checked but
for one its signature names nowhere (#618): openverse's reading was that a
call's expected result may give it (`Make():?t`).

**openverse now.** `checkDeterminedTypeParams` (`Elab/Signatures.lean`),
after the signatures are declared and the Book's variances computed
(`elabProgramCore`, between `declareSignatures` and `inferSignatures`),
refuses a source function (or method) with a type parameter so given by
nothing: "no parameter of F determines its type parameter t, so no call can
give it one …" (the source check of #618, `UpperBounds.checkDetermined`,
keeps refusing earlier one named nowhere, and a bounded one no parameter
names). The compiler's own functions, whose names have `$` (the branches
of refining casts, `$refine…`; adapters, stages, helpers), are no program's
and keep the reading: their calls are the compiler's, which writes the
expected type there.

**Programs.** 45 tests of `tests/verse` and 3 of `tests/errors` declared
such a function; 43 rewritten keeping their subjects, their output the
same (the list is the commit's): 27 refining-cast context tests
(`class_cast_context_*`) declared an unused constructor helper
`Pair(N:int where a:type, b:type):pair(a, b)`, dropped, the three of a
field's default constructing `pair(a, b){}` instead (and the generator of
the size test, `tests/scripts/test-choice-size.sh`, the same); a function
of a contravariant class's type parameter takes it as a type argument
(`Show2(t:type, S:shower(t))`, `Run(t:type, P:base(t))`, `Read(t:type,
X:i1(t))`) or names the type (`GQ(X:j0(?string))`); a result-only
`Empty(N:int where t:type):[]t` takes its type from a parameter
(`Empty(N:t)`, `Empty(Like:[]t)`); `Nothing(t:type):?t` and a `Fail` of
result `false`. Deleted, as their subject was the retired reading:
`fn_values_open_tuple_empty` (generic function values with no parameters,
their type parameter from the function type expected) and
`multi_generic_mutual_result_type` ("The other member's type comes only
from its result"). Two error tests that refused such a function at its call
(`generic_uninferable`, `multi_generic_tp_unbound`) refuse it where it is
declared. The models `gadt_function_values` and `gadt_method_instances`
wrote `Empty(N:int where …):[]a`; they write `Empty(N:a)` now (their random
stream the same; 1,000 seeds each agree in Lean, C and the model), so the
4 generated programs of `corpus2` that had it are refused now.

## `using{/localhost}`

**The rule.** A `using` does not name `/localhost` or a path below it.

**The Book.** The tests, `Tests/Modules/Using2.versetest`: "Explicitly
using a "/localhost" package is not allowed." (`:84-86`, `using{/localhost}`,
3544 and 3587), "Explicitly using something in a "/localhost" package is
not allowed." (`:88-90`, `using{/localhost/something}`), and
`using{/localhostkinda}` refused for naming nothing (`:92-94`, 3587 only).
Ch. 16 (`16_modules.md:349`): "all imports must be resolvable when your
code is compiled".

**openverse before.** A `using` of a path was accepted and ignored.

**openverse now.** The parser writes `using{/localhost…}` as a refused
form (`Refused.localhostUsing`), which `Attributes.apply` refuses first.
**Left:** a `using` of any other path that names nothing
(`using{/localhostkinda}`, 1 case): openverse has no registry of the paths
it stands in for.

## `<>` is left-associative

**The rule.** `<>` is left-associative: its left operand is the
comparisons before it, whose value is their leftmost operand, so `1 <> 2
<> 1` is `(1 <> 2) <> 1`, which fails. The other comparisons chain: each
checks the operand before it, `0 <= X <= 9` checks `0 <= X` and `X <= 9`.

**The Book.** The tests, `Tests/Operators/Associativity.versetest`: "Test
that <> is left associative." (`:6`), `assert{1 <> (2 <> 1)}`,
`assert{not (1 <> 2) <> 1}`, `assert{not 1 <> 2 <> 1}` (`:7-9`); and for
`<`, `<=`, `>`, `>=`, "left~~right~~ associative" (`:11-33`), `assert{not
1 < 3 < 2}`, which a left-associative `<` would pass and a chain fails.
The prose: "comparison operators return their left operand when the
comparison succeeds, and comparison chains have special syntax that checks
all adjacent pairs" (ch. 1, `01_expressions.md:890-891`), "Verse does
**not** evaluate the comparison chain `A <= B <= C` as `(A <= B) <= C`"
(`:905-907`); the precedence table makes them right-associative
(`04_operators.md:50`).

**Where the Book disagrees with itself.** For `<>` (already on [the
wiki](https://github.com/rudi-cilibrasi/openverse/wiki/Where-the-Book-disagrees-with-itself),
"Comparison chains with `<>`"): the prose chains every comparison, its
tests make `<>` left-associative. openverse follows the tests. (For `=`,
a chain and left association agree: `1 = 1 = 1`, `:4`.)

**openverse before.** A chain for every comparison: `1 <> 2 <> 1` checked
`1 <> 2` and `2 <> 1`, and succeeded.

**openverse now.** `parseCmp` (`Front/Parser.lean`) makes a `<>` that
follows a comparison the outer comparison of what precedes it: `A < B <>
C` is `(A < B) <> C`, which checks `A < B`, then `A <> C`. Programs: 46
generated programs of corpus2 (the `mv` model: `mv-plain` 23, `mv-rec` 9,
`mv-bif` 7, `mv-mv` 7) write a `<>` after another comparison, and compile
to other code; the model (`scripts/models/mv.py`) now compares the
leftmost operand at such a `<>`, its random stream the same.

## An empty container with no type from its context

**The rule.** `array{}` with no element type from its context is an array
of `false`, the type with no values, below every type (Book of Verse ch.
2): `[]false`, which converts to every array type; `map{}` likewise is a
`[false]false`, and `Concatenate()` a `[]false`. An operand of `false` type
of an arithmetic operator has the other operand's type (`X + Y` with `X`
an element of an empty array).

**The Book.** The tests: `A1:=array{}; A2:=A1+array{1}; A2=array{1}`
(`Tests/Array.versetest:90`), `not array{}.Last[]` (`:154`),
`array{}.Remove[0, 0]=array{}` (`Intrinsics/ArrayRemove.versetest:7`),
`array{}.ReplaceAll(array{20}, array{50})=array{}`
(`ArrayReplaceAll.versetest:10`), `Concatenate()=array{}`,
`Concatenate(array{})=array{}` (`Concatenate.versetest:4-8`),
`X := array{}; X = ""` (`Literals/String.versetest:181`), `array{}+""=""`
(`Operators/BinaryAddString.versetest:23`), `Array:=for(X:array{},
Y:array{1}) { X+Y }; Array=array{}` (`FlowControl/for.versetest:114`),
`Map:=map{}; Map=map{}` (`Map.versetest:236`). Ch. 1 writes `Empty :=
array{}` (`01_expressions.md:1274`, a tested example).

**Where the Book disagrees with itself.** Ch. 3: "Without a type
annotation, the compiler cannot determine what type of array you want, so
you must either provide the type explicitly or include at least one element
that establishes the type." (`03_containers.md:273`); ch. 1 and the tests
above take `array{}` with no type. openverse follows the tests.

**openverse before.** "the type of an empty array{} must be given", and
of a `map{}`; `Concatenate()` needed an expected type.

**openverse now.** The literal's type is `Ty.never` inside an array or a
map (`elabE`'s `arrayLit`, `elabMapLit`), which `coerce` takes to any
array or map type (its elements' conversion never runs); `Concatenate`
takes and gives one (`elabConcatenate`), and an arithmetic operator's
operand of type `never` takes the other's type.

Programs: three of openverse's error tests refused an empty literal with
no type from its context, and are valid programs now: they are tests of
`tests/verse` with their output (`empty_literal_int`, `array{} = 0`, which
fails, a comparison of two types; `if_clause_both_untyped` and
`if_clause_refining_untyped`, an `if` of two empty arrays, or of one and an
int, as a statement). Every program that compiled before keeps its code:
where an expected type is found by trying again with another's
(`argNeedsType`'s probe, `ConcatenateMaps`, `Concatenate`), a type of
`false` says nothing, and an empty literal of it converts as its literal.

## Generators in `first`, and a range's typed binding

**The rules.** `first` takes generators among its clauses as `for` does,
`X : Xs`, `I -> X : Xs` and `X := a..b`: the first iteration whose clauses
succeed gives the body's value, and what the failed iterations' clauses did
is undone. A range's binding may state its type, `int`, in `for` and
`first`: `X:int := a..b`, `X:int = a..b`.

**The Book.** Ch. 7, "First Expressions" (`07_control.md:923-1010`): "The
`first` expression is similar to `for`, but instead of evaluating its body
for every successful iteration, it evaluates the body only for the
**first** iteration of the domain clause that succeeds" (`:923-925`), "If
no iteration reaches the body, `first` fails" (`:927`), "The `first`
expression uses
the same binding syntax as `for`" (`:972`), `first(I -> V : Arr, V =
Target). I` (`:982`). The tests, `Tests/FlowControl/first.versetest`:
`first(I->Y:Xs; X = Y){I}` (`:14-31`), the dot and `do` forms (`:54-65`),
`1 = first(FirstPassesFilter[], I:=1..3) { I }` (`:36-51`), a failed
iteration's effects undone, `FirstPos2(20, array{10,20,30,20}) = (1, 1)`
(`:107-120`), nested generators with counters (`:122-143`),
`first{X:Xs; X>0}` (`:191-203`). A typed range binding:
`List:[]int= for(X:int=2 .. 3) { X }` (`FlowControl/for.versetest:17`),
`for (i:int := 0..Nums.Length)` (`Exercises/TwoSum.versetest:20`).

**openverse before.** "a generator X : source in first is not supported
yet", "a range a..b can only be the source of a for clause" (in `first`,
and typed in `for`).

**openverse now.** The parser writes each generator among `first`'s clauses
as the choice of its source's elements (`firstOf`, `Front/Parser.lean`):
`X : Xs` is `X := $each(Xs)`, which the elaboration of a choice's binding
takes one element at a time, the clauses after it in the filter
(`elabOneGo`, as for a recursive function's values, #235); `I -> X : Xs`
binds the source once, then `I` to the choice of its indices and `X` to
the element; `X := a..b` is the choice of the range's ints. A `for`'s range
binding takes a stated type `int` (`elabSource`, `Elab/For.lean`).
**Left:** `first{X:=1..5, 3*X>10}`, whose clause is a tuple of a range's
binding and a value (`first.versetest:206`), and a generator over a map in
`first`.

With a generator, a filter that cannot fail is refused: "Only allow
expressions that can fail (same as `for`)" (`first.versetest:28-31`,
`first(I->Y:Xs; X = Y; I){I}`, 3513), by the rule of a `for`'s filters
([every filter of a `for` can fail](book-remaining-rules.md#every-filter-of-a-for-can-fail);
a literal or a name, `checkFirstFilters`, before it). In `first{…}` a comma joins the
clauses around it into a tuple: "Comma is not the same as semicolon",
`(4,12) = first{X:=1..5, 3*X>10}` (`:204-208`), where openverse's clauses
keep commas as separators; with a generator among them the parser refuses
the comma ("a generator inside a tuple is not supported yet"), so that the
case is refused, not given another value. Programs: the error test
`first_generator` is a valid program now, in `tests/verse` with its output.

## `false` as a type

**The rule.** `false` written as a type is the type with no value, below
every type: a function whose result is `false` never returns, and an array
of it has no elements and converts to every array type.

**The Book.** Ch. 2, "void, true, tuple() and false"
(`02_primitives.md:1233-1300`) and the API (`Err(…)<computes><predicts>:false`);
the tests: `Suspend()<suspends>:false = Suspend()`
(`Bugs/2026-01-26-FindFirstAsyncSubExprMissingOverrides.versetest` 5, 21,
28), `ParametricTypes.versetest:711`.

**openverse before.** "unknown type 'false'"; the type existed inside
(`Ty.never`, of `return`, `break`, `Err()`), with no name.

**openverse now.** `resolveTy` names it; a call of a function whose result
is `false` converts to any type as the other values of that type do
(`coerce`, a `void` in Verse Core followed by `Err()`, never reached). No
program's code changes. `true` as a type: [below](#true-as-a-type).

## Localized messages

**The rule.** A definition marked `<localizes>` is a message: a constant
`X<localizes>:message = "text"`, a function
`F<localizes>(Name:string, Number:int):message = "Hello {Name}"`, or a
field of a class or an interface; `Localize(M)` renders one into a string,
`Join(Messages, Separator)` makes one of several. Its type is written, and
is `message`; its value is a string literal; an interpolant in it is a
parameter's name or a code point; every parameter is an `int`, a `float`, a
`string` or a `message`.

**The Book.** Ch. 12, "Localization" (`12_access.md:885-1100`): "Three
parameter types are supported: `string`, `int` (formatted with comma
separators), `float`" (`:917-920`), "Use `{ParameterName}` to insert
parameter values … Only parameter names and Unicode code points allowed in
braces" (`:922-925`), `Localize(HighScore(190091)) = "New record: 190,091
points!"` (`:968`), named parameters with defaults (`:984-990`), tuple
parameters (`:1009-1014`), "Localized messages **must be defined at module
or snippet scope**" (`:1070`), and overrides in classes (`:1095-1110`).
The API: `Localize<public><native>(Message:message)<reads>:string`,
`Join<native><public>(Messages:[]message, Separator:message)<transacts>:message`,
`message := class<epic_internal>` with a key, its default text and its
substitutions. The tests, `Tests/Localization.versetest` (forms 2, 4 and 6
valid, 1, 3 and 5 refused, 3639; a value that is no string literal 3638; a
parameter of a class or an option 3509; a message in a function 3651;
`{"print"}` 3652; `{Abc}`, a name that is no parameter, rendered as
written, `:162-166`), `LocalizationJoin.versetest`, `Bugs/SOL-3887…`,
`Bugs/SOL-3734…`.

**openverse before.** "unknown or unsupported specifier <localizes>".

**openverse now.** `Localization.desugar` (`Front/Localization.lean`),
step 0 of `admitSource`: a message is its default text rendered, as
openverse has no culture to render it in, so a `message` is a `string`
(`resolveTy`, when the program defines no type of that name); a
`<localizes>` definition loses the specifier, its text's interpolants the
parameters' rendered values, computed once for every parameter by the
helper `$localizeValue` (an `int` with comma separators, a `float` by
`ToString`, a `string` as it is; a parameter of another type has none, as
the tests' "No overload of the function `MakeLocalizableValue`"), a name
that is no parameter its text in braces; `Localize` and `Join`, when the
program defines none, are calls of the helpers `$localize` and
`$localizeJoin`. **Not pinned:** a float's format in a message (no test:
`ToString`'s six decimals here); a message is a `string`, so a string is
accepted where a message is expected, which Verse refuses (no test).

An empty `map{}` with no type from its context, a `[false]false`, joins
another map at that map's type (`joinTy`) and converts to it as the empty
map (`convert`): `M1 := map{}; ConcatenateMaps(M1, map{0=>"0"})`
(`Map.versetest:240`). **Left** (2 cases): `false + array{}` where a `[]int`
is expected (`Array.versetest:108`: `false`, a `logic`, is no operand of
`+`), and `array{}.ReplaceAll(array{}, array{})` (`ArrayReplaceAll.versetest:12`:
the helper's type parameter, which only arrays of `false` meet, is not
inferred).

## `true` as a type

**The rule.** `true` written as a type is the type of the empty value
alone, as `tuple()` is: `false` and `()` are its values, a `void` value
converts to it, and it converts to `logic` (as `false`), to `void` and to
an empty array. `void` and `true` are one type inside options, arrays and
maps: `?void` converts to `?true`, `[]void` to `[]true`, `[int]void` to
`[int]true`; a `void` value converts to `logic` as `false`, as `true`'s
does. A `branch:`'s value is an `any`: `void` and `any` take it, `true`
does not. `X:true = 1` is refused, as `X:tuple() = 1` is.

**The Book.** Ch. 2, "void, true, tuple() and false"
(`02_primitives.md:1232-1310`): "Verse has a single "there is nothing
interesting here" value. It can be written `false` or `()`, and the types
`void`, `true` and `tuple()` all describe it. These are interchangeable"
(`:1234-1236`), `Flag:true = false` (`:1253`), "`true` is a subtype of
`logic`, so the unit value flows into logic positions" (`:1261`), "and
`void`/`true` interchange through optionals, arrays and maps"
(`:1294`, `MaybeTrue:?true = MaybeVoid`). The tests,
`Tests/Void.versetest`: `?void` to `?true` (`:50`, `:56`), `[]void` to
`[]true` (`:68`), `[int]void` to `[int]true` (`:80`), `F:int->true =
VoidOutput` (`:100`), the joins of `int->true` and `int->void` values
(`:161`, `:165`) and of `(:true)->int` and `(:void)->int` ones (`:169`,
`:173`), `X:true = false` (`:177`), `X:logic = if (false?) then () else
true` (`:215`, `:219`), `[]true` and `?true` where a type parameter is
`[]void`, `?void` (`:253`, `:267`); `F1(X:void)<computes>:true = X` and
`set X = I()` with `I():void` into `var X:true`
(`Bugs/FORT-1054384-Void-Any-Meet.versetest` 17-25); and
`Result:true = branch: …` refused (3509) where `Result:any = branch: …`
is valid (`Bugs/FORT-582630-BranchResult.versetest` 3-14): a `void`
converts to `true`, so a `branch:`'s value is no `void`.

**openverse before.** "unknown type 'true'"; `tuple()` was the type (with
`void` converting to it at the top only), `void` did not convert to
`logic`, and a `branch:` gave `void`.

**openverse now.** `resolveTy` names `true` `tuple()`; `convert` takes a
type to the same type with `tuple()` for some of its `void`s inside
options, arrays, maps and tuples (`Ty.unitUp`; one Verse Core type, so no
code), and `void` to `logic` (`false`); `joinTyShaped` joins two such types
at the one with `tuple()`, and `join` an `if` with a `void` branch where a
`logic` is expected at `logic`; `elabBranch` types a `branch:`'s value
`any` (its code the same; in a program where an `any` prints itself,
`ToDiagnostic`'s, the empty value's object). Programs: those listed in the
commit whose code changes.

**Left.** `true` and `void` in a function type (`Void.versetest` 100,
161, 165, 169, 173: `F:int->true = VoidOutput`, `if (…) { TrueOutput }
else { VoidOutput }`): `int->true` is `int->tuple()`, another instance of
the function shape than `int->void`, and the classes a call of a function
value dispatches to are those at its type's arguments exactly. Making a
shape's `tuple()` its `void` breaks openverse's empty-tuple parameter, a
function of no parameters taken as one of a `tuple()` parameter
(`fn_values_open_tuple_small`, #231), so it needs the dispatch to relate
shape instances whose arguments differ in `void` and `tuple()` alone (one
Verse Core type). `true?`'s value, below.

## The value of `true?`

**The Book disagrees with itself** (already on [the
wiki](https://github.com/rudi-cilibrasi/openverse/wiki/Where-the-Book-disagrees-with-itself),
"The value of `X?` on a `logic`"): ch. 8 (`08_failure.md:57`) "succeeds
with that value", and ch. 4 "equivalent to comparing against true";
the tests make it the empty value: `assert{true?=false}`, `assert{not
true??}` (`Tests/Operators/BoolQuery.versetest` 3, 4), `(true? and true?) =
false` (`Operators/LogicalAnd.versetest:29`), `x := true? or true; x =
false` (`Operators/Precedence.versetest:121`), as ch. 2's `true` type has
it. openverse follows the tests, in design: **left.**

**The design.** `X?` of a `logic` is of type `true` (`tuple()`), its code
`(query X; ())`. Every program that writes `X?` would then change its
code, the elaborator's own `true?` clauses too (`ExpressionControl`'s
`tq`): in a condition, a filter, a statement, `not`, `logic{…}`, the left
of `or` and a `<decides>` body's clauses, whose value is dropped, the
`()` must not be written, so those contexts must elaborate the query as
before (a flag on `Ctx` that a value-dropping context sets, or the query
written as before and converted where its value is taken: a binding, an
argument, a comparison's operand, a result, an operand of `and`). Then
only the programs that take the value change, and the four cases agree.

## A map literal's values with nothing in common

**The rule.** With no value type expected, a map literal whose values
have nothing in common joins them as an array literal's elements: at
`comparable` when every one is comparable, else at `any`.

**The Book.** The tests: "Test that the result of a map literal with
values of disjoint types is coerced to [key_type]any." (`Any.versetest:131`),
`map{0=>"0", 1=>1.0}.Length=2` (`:133`), `map{0=>"0", 1=>1.0,
2=>array{0,1,2}}.Length=3` (`:134`); "Disjoint value types are allowed."
(`Map.versetest:160-164`, `M:=map{"0"=>0, "0.0"=>0.0}` returned as a
`[string]any`). Ch. 1 joins an array literal's disjoint elements at
`comparable` ("their common supertype"), which openverse keeps for both.

**openverse before.** "the values of this map have different types".

**openverse now.** `elabMapLit` (`Elab/Expr.lean`) joins them at
`fallbackJoin`'s type when none is expected and the join is not ambiguous.
No program that compiled changes.

## A `for` body at the element type expected

**The rule.** A `for` whose values are not of the element type expected
has its body elaborated at that type, as a typed binding is: `false`
there is an empty option.

**The Book.** The tests, `Bugs/SOL-4137-MemoryLeakCreatingA3dArray.versetest`:
`var Data:[][][]?int = for (x := 0..1): for (y := 0..2): for (z := 0..2):
false` (`:4-9`, a field's default) and a function of result
`[][][]?int` whose body is the same (`:15-21`).

**openverse before.** The body was elaborated with no expected type:
`false` a `logic`, the `for` a `[][][]logic`, refused.

**openverse now.** `elabECore` (`Elab/Expr.lean`): when a `for`'s value
does not convert to the array type expected, the `for` is elaborated
again with its body at the element type (a typed binding of it); when that
is refused too, the first stands, refused as before. No program that
compiled changes.

## `Args` bound by a program

**The rule.** `Args`, openverse's command-line arguments (not the Book's),
is added only when the program neither defines nor binds the name itself.

**The Book.** The tests bind it as a local: `Args : tuple(int, int) = (1,
2);` (`DefaultNamed.versetest:274`), `Args:[]float = (-Inf, 0.0, Inf)`
(`Math/Math.versetest:84`).

**openverse before.** "'Args' is already the name of a function or
constant" (the command line's `Args` and the local in one program).

**openverse now.** `argsAndMethodOverloads` (`Elab/Source.lean`) adds it
unless the program defines it or binds it (a local, a generator, a
parameter). No program that compiled changes.

## `set` through a call's result or a construction

**The rule.** A `set` path may start at a call's result or a
construction: the root is evaluated first, then the path's keys, then the
value. A key of several values is a tuple's: `set M[1, 2] = 1` is `set
M[(1, 2)] = 1`.

**The Book.** The tests, `Tests/AssignmentSequencing.versetest`: `set
EffectfulIdentity(Y, X).Contents = Y.Contents; X.Contents = 1` (`:17`,
the root's effect before the value), `Z := set … = …; Z = 1` (`:23`), and
with a map's key whose computation has effects (`:38`, `:44`: root, key,
value); `set c0{}.X += "def"` (`Bugs/FORT-779650-…versetest` 27);
`set ObjectMap[1,2] = 1` with `ObjectMap:[tuple(comparable,
comparable)]int` (`Map.versetest:472`). Ch. 5 is silent on the order.

**openverse before.** "openverse supports set X = …, and set on a path of
fields, indices and keys from a variable".

**openverse now.** `elabSet` (`Elab/Expr.lean`) binds such a root to a
name of its own first (`$setRoot…`, a block `{R := root; set R.… = v}`),
and writes a path's key of several values as their tuple. No program that
compiled changes. **Left:** `set live` (VerseVM's live variables).


## A `<persistable>` struct's enum

**The rule.** An enum persists only when it is `<persistable>`: a
`<persistable>` struct's field, and the value of a module-scoped `weak_map`
keyed by a `<persistent>` class, may be of an enum only when the enum is
`<persistable>`.

**The Book.** Ch. 17 (`17_persistable.md:190`), among what cannot persist:
"Non-persistable enums - Enums without `<persistable>` specifier cannot be
used". The tests: `enum1 := enum: A` as a field `G:enum1` of a
`struct<persistable>` is refused (`Tests/persistable.versetest:59`, 3662),
as are the struct's other fields that do not persist (`:51`, `:55`, `:65`).

**openverse before.** The parser took an enum's `<persistable>` and dropped
it, and every enum was taken to persist.

**openverse now.** An enum keeps its specifiers (`SExpr.enumDef`'s list:
`<open>`, `<closed>`, `<persistable>`), and the two places that ask what
persists, a `<persistable>` struct's fields (`typeEnvironment`) and a
module-scoped variable's value (`ModuleVars.Defs.persists`), take an enum
when it is `<persistable>`. No program that compiled changes: none of
openverse's tests, generators or the corpus has an enum where a value must
persist.

## `void` given as a type argument

**The rule.** `void` given as a type argument of a program's parametric
class, interface or struct, written as a type or as a parent, is `true`:
the type parameter bound to it takes the empty value alone. Inside the
argument, `void` in an array, an option, a map's value or a tuple is
`true` too (`box([]void)` is `box([]true)`); a function type's `void` stays
(the shapes of `int->void` and `int->true` are two, [`true` as a
type](#true-as-a-type)). A parameter or a local written `:void`, `:[]void`,
still takes any value.

**The Book.** Ch. 2, "Write the value, not the type name"
(`02_primitives.md:1311-1316`): "`void` names a type; the unit value is
`false` (or `()`). A parameter declared literally `:void` accepts any
value, so passing the type name happens to work there. It does not work
when `void` reaches the parameter through a type parameter, so write the
value", with the tested example `holder909(void)` refusing
`C.Method(void)` and taking `C.Method(false)`, and the warning
(`:1354-1359`) that the error "reads *"expects a value of type `true`…"*".
"Conversion is one-way" (`:1371-1374`): "Any value converts to `void`, and
that extends through containers in ordinary parameter positions —
`[]int` satisfies `[]void`. A *type parameter* bound to `[]void` is
invariant, though, so only `[]void` (or `[]true`) fits there", tested with
`box([]void){}.Put(Y)` refused for `Y:[]int`. The tests,
`Tests/Void.versetest` 227-279: `class1(void){}.Foo(false)`, `.Foo()` and
`.Foo(X)` with `X:void` valid, with `X:int` refused (`:246`, 3509);
`class1([]void){}.Foo(X)` valid with `X:[]true`, refused with `X:[]int`
(`:260`) and `X:?int` (`:274`); `class1(?void){}.Foo(X)` valid with
`X:?true`. Prose and tests agree.

**openverse before.** A type argument `void` took any value, as `void`
written in place does.

**openverse now.** `TyEnv.typeArgs` (`Elab/Context.lean`) gives a
program's parametric type, where `resolveTy` resolves its application, its
arguments with `Ty.voidArg`, and `classHierarchy` gives a parent's
arguments `STy.voidArg` (so an inherited field or method is at `true`
too). The library's types, the concurrency prelude's `task` and events
(`PreludeNeeds.names`), keep `void`: `task(void)` is a spawn's of a `void`
function. Messages say `tuple()`, openverse's name of the type.

## `(q:)M(…)` in an override of `M`: warnings 2003 and 2004

**The rule.** In a method that overrides `M`, a call `(q:)M(…)` of `Self`
whose overload is the slot the method implements is a warning: it
dispatches on `Self`'s class, so it calls the override itself again. The
warning is 2003 ("should use super") when `q` is what `(super:)M` reaches,
the implementation above, or the slot's interface when nothing above
implements it, and 2004 when `q` is further up, which `(super:)` cannot
reach. The program compiles.

**The Book.** The tests alone,
`Tests/Bugs/SOL-3564-CallingSuperClassMethodFromOverriddenMethod.versetest`:
`F<override>():void= (a:)F() # 2003 - should use super` (`:7-12`); with
`b` overriding between, `(a:)F() # 2004 - you can't reach a: as super:`
(`:18-26`), likewise through an interface (`:32-40`, "ia: is not the
immediate base override"); over an abstract class that does not implement
it, `(ia:)F() # 2003 - should use super:` (`:45-52`); a qualified new
method `(b:)F` calling `(a:)F()` is valid, "ok because we're not in a
vcall scenario" (`:57-76`), and so are a call of another overload
(`:139-146`) and a method's own qualifier in one that overrides nothing,
"intentional recurrsion" (`:167-170`). The prose is silent.

**openverse before.** Accepted, with no warning; such a call recursed
until the fuel ran out.

**openverse now.** `warnQualifiedSelfCall` (`Elab/Application.lean`),
where `elabMemberApp` takes a method call through a value: a call written
`(q:)M` of `Self`, in a method `M` of `Self`'s class whose slot is
introduced above it (an override), whose slot the call's is, warns with
`warnAt`; which of the two by `superImpl`, as `(super:)M` resolves. The
cases `:57`, `:66` and `:80` reach openverse's refusal of a second method
of one name first (`(b:)F` beside the inherited `F`, [After classes and
subtyping](book-test-conformance.md#after-classes-and-subtyping)). No
program that compiled changes but those that write such a call, which now
warn.

## An enum's value named after a reserved word

**The rule.** An enum's value takes a reserved name (`reservedNames`: the
names the Book's tests reserve, the built-in names and the effects') or an
access specifier's name (`public`, `internal`, `protected`, `private`,
`epic_internal`) only qualified with its enum, `(A:)public`; unqualified it
is refused.

**The Book.** Ch. 9 (`09_structs_enums.md:530-553`): "Qualification also
allows you to use reserved words and keywords as enum values, which would
otherwise cause errors", with the tested example `bad_enum19 := enum:
public` (3532) and `(keyword_enum:)public  # OK: reserved word
qualified`, "without qualification each of those three is an error". The
tests, `Tests/QualifiedIdentifier.versetest`: `A := enum{ (A:)public }`
valid, "even if they alias a reserved word" (`:313-314`), and `A := enum{
public }` refused (`:315-316`, 3532), as `enum{ for }` is (`:320`, 3514).
The test calls `public` "a reserved word with a built-in symbol" and `for`
one "with no built-in symbol" (`:314`, `:319`): the access specifiers are
the built-in symbols the chapters name; openverse takes them and its
reserved names.

**openverse before.** An enum's values were not among the names
`checkReservedNames` reads, so `enum{ public }` and `enum{ decides }` were
accepted.

**openverse now.** `checkReservedNames` (`Elab/Source.lean`) reads each
enum's unqualified values. No program that compiled changes: none of
openverse's tests, generators or the corpus names an enum's value so.
