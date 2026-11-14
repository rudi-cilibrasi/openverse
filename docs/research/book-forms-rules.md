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
