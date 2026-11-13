# Empty parentheses (Book of Verse tests: `class<castable>()`, `interface() {}`,
# `c1():=class{X:int}` used as `c1()`): `class()` has no parents, as `class`;
# `t()` gives no type arguments, the type `t`, and `t(){…}` is `t{…}`.
base := class() {}
T := interface() {}
c1() := class(base, T):
    X:int = 1
F3():c1() = c1(){X := 10}
Main():void =
    Print("{F3().X}")
