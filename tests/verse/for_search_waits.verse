# What a for undoes, with a body that waits (docs/DESIGN.md, "What a for
# undoes: one search"): the search's steps run between the bodies, so the
# body runs outside every failure context and may wait; what the search did
# for an element whose later generator gives nothing is undone.
Main()<suspends>:void =
    var T:int = 0
    for (I := 1..3, (set T += 10 * I; true?), (Print("i {I}"); true?), J := 3..I):
        Sleep(0.01)
        set T += 1
        Print("body {I} {J} {T}")
    Print("t {T}")
