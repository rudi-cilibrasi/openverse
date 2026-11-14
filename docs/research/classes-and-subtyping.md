# Classes and subtyping: the Book's rules

The rules behind the causes about classes and subtyping of the Book test
survey ([book-test-conformance.md](book-test-conformance.md), "Classes and
subtyping: the map"), pinned with the Book's words, one section per form
built. The Book is the pinned revision `beaa719b`; chapter lines are of its
`docs/`, test lines of its `Tests/`. Where the prose and the tests
disagree, openverse follows the tests, and the section quotes both.

## Recursive parametric types

**The rule.** A parametric class or interface may name itself in the types
of its fields only at its own type parameters, in their order, and no
parametric class or interface may name another one in its fields that
names it back, directly or through others.

- Ch. 10, "Recursive Parametric Types" (`10_classes_interfaces.md:1494-1497`):
  "Parametric classes can reference themselves in their field types, …
  The key requirement is that the self-reference uses **the same type
  parameter** — this is the only form of recursion Verse allows."
- "Disallowed: Polymorphic Recursion" (`:1578-1581`): "Polymorphic
  recursion occurs when a parametric type references itself with a
  **different type argument**", with `Next:my_type(?t)` and
  `Next:?bi_list(u, t)` ("parameters swapped") as its errors.
- "Disallowed: Mutual Recursion" (`:1609-1612`): "Mutual recursion between
  multiple parametric types is not supported either; each of the two
  definitions below is rejected on its own".
- The tests: `ParametricTypes.versetest` 262-271, "Polymorphic recursion is
  not yet supported", "Mutual recursion is not yet supported", 3509 each.

The prose and the tests agree. The rule is about field types (the
chapter's words and every example); a method's signature is not looked
at. Classes without type parameters may name each other (ch. 10's linked
structures). The types the front end writes (named with `$`: closures,
type values) are not looked at.

**In openverse.** `checkParametricRecursion` (`Elab/Classes.lean`), with
the class hierarchy (phase 4), after the inheritance cycles: each
parametric class's own fields, those with accessors too, are walked for
applications of parametric classes and interfaces (`STy.applicationsOf`,
over `STy.children`); one of itself at other arguments is refused, then a
cycle among the others.

```verse
my_type(t:type) := class:
    Value:t
    Next:?my_type(?t) = false
```

`field 'Next' of my_type names my_type(?t), my_type at other type
arguments than its own: a parametric type refers to itself only as
my_type(t) (Book of Verse ch. 10, "Disallowed: Polymorphic Recursion")`;
and for `t1(t)`'s `Next:?t2(t)` with `t2(t)`'s `Next:?t1(t)`: `the fields
of t1 name t2, and those of t2 name t1: parametric types cannot be
mutually recursive (Book of Verse ch. 10, "Disallowed: Mutual
Recursion")`.

**What changed.** An interface with `Next:n([]t)` was refused when a
variable of its type needed a placeholder (#157); it is refused where it
is defined now (`tests/errors/iface_placeholder_grows.verse`, renamed
`parametric_recursion_interface.verse`). `tests/errors/class_param_const_mutable.verse`
named `w(cell(int))` inside `w(t)` to reach an object with a `var` field;
it reaches it through a `holder(cell(int))` now, with the same message.
