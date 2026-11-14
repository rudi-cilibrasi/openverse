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
