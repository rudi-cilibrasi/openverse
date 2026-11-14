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
