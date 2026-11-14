# Path literals (Book of Verse ch. 1, "Path Literals"; ch. 16, "Paths"): a
# '/' where an operand starts, before a letter or digit, begins a path; after
# an operand (a name, a literal, a closing bracket) it divides. A path in
# using{…} of a package openverse knows (the Verse library's, the engine's)
# is accepted and ignored; any other names nothing, and is refused.
using{/Verse.org/Simulation}
using { /Verse.org/My-Module.v2/Sub/(/a/b:)c/d'+' }

Main():void =
    X := 12
    if (A := Floor(X/3), B := Floor((X)/4), C := Floor(X /6), D := Floor(X / 12)):
        Print("{A} {B} {C} {D}")
