# Rules of the forms of expressions, statements and the library

The rules openverse takes from the Book of Verse for the causes of [the map
of forms](book-test-conformance.md#forms-of-expressions-statements-and-the-library-a-map),
each pinned with the Book's words, its prose and its tests, at the
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

## A type parameter named nowhere

**The rule.** Every type parameter of a function is named in its
signature: in a parameter's type or in its result's. (A bounded one, or
one a bound names, must be determined by a parameter, as before.)

**The Book.** The tests (3503): `F(:u where t:type, u:type):void = {}`
refused (`Tests/ParametricFunctions.versetest:374`), beside `F(() where
t:type):?t` (`:338`) and `F(() where t:type):[]t` (`:341`), refused too,
and `G(() where t:type):(t->void) = F` valid (`:376-378`). The prose is
silent.

**openverse before.** A type parameter without a bound was not checked:
openverse's reading is that a call's expected result may give it
(`Make():?t`, LANGUAGE.md, "Readings"), and one its signature names
nowhere, which nothing can give, was accepted.

**openverse now.** `UpperBounds.checkDetermined` refuses a type parameter
without a bound that its signature names nowhere: "the type parameter t of
F is named nowhere in its signature, so nothing can give it one". Programs:
the error tests `fn_value_open_phantom`, `fn_method_instance_phantom`,
`fn_method_tuple_phantom` and `fn_context_method_phantom`, whose functions
had such a type parameter for another refusal, are refused for it now
(their expected message rewritten); `alias_type_parameter` names its type
parameter (`Id(X:t where t:type):t`), so that what it refuses is still a
type parameter that takes a type alias's name; the test
`fn_values_method_instance_unused` names its method's (`D:?u`), its output
the same.

**Left:** the rest of the tests' rule, that a parameter, not the expected
result, gives every type parameter (`:338`, `:341`, which openverse's parser
refuses for their empty parameter group, and `F(G(:t):void where t:type)`,
`:348`, named only in a function type's parameters). Measured, it refuses
54 of openverse's tests of its reading (`class_cast_context_*`,
`fn_values_open_*`, `generics`, …), 33 functions the compiler writes (the
branches of a refining cast, `$refine…`), and 4 generated programs of two
models (`gadt_function_values`, `gadt_method_instances`): an owner's
decision to retire the reading. And the tests split by VM there: VerseVM
takes `MakeClosure(Callback:tuple(payload, context)->void, Context:context
where payload:type, context:type):(payload->void)`, whose `payload` only a
function type's parameter names
(`Bugs/FORT-592189-MaybeCoerceToTypeCrash.versetest:44`, `verse_vm_only`),
where the BPVM's twin is an IR error (`:4`).

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

With a generator, a filter that is a literal or a name, which cannot fail,
is refused: "Only allow expressions that can fail (same as `for`)"
(`first.versetest:28-31`, `first(I->Y:Xs; X = Y; I){I}`, 3513;
`checkFirstFilters`, `Elab/Source.lean`). In `first{…}` a comma joins the
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
program's code changes. **Left:** `true` as a type (10 cases:
`Void.versetest` 50-177, 253, 267, `FORT-1054384…`): the type of the empty
value alone, as `tuple()`, which `void` must not convert to (the tests
refuse `Result:true = branch: …`, `FORT-582630-BranchResult.versetest:3`,
3509), while `()` and `false` must (`Flag:true = false`, ch. 2,
`02_primitives.md:1240`): openverse types `()` as `void`, so `true` needs
the empty tuple's literal typed `tuple()` first.

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
