# The clauses of if and for may be written in parentheses, or as {…}, `:` and
# an indented block, or `.` and an expression; without parentheses, `then`
# (for `if`) or `do` (for `for`) and a branch may follow, and without it the
# form is the clause macro (`if{c}`, `if{c} else e`, `for{c}`). Book of Verse
# tests: `if:` with no `then`, `for:` … `do:`, `if. 1 > 2 then. …`,
# `if {…} then {}`.
Sum(Xs:[]int):int =
    var S:int = 0
    for:
        X:Xs
        X > 1
    do:
        set S += X
    S
Main():void =
    var Num:int = 123
    if:
        1 < 2
        set Num = 42
    else:
        set Num = 56
    var A:int = 0
    if:
        set A = 1
        Num = 0
    if. 1 > 2
    then. set Num = 7
    else if. 3 > 4
    then. set Num = 8
    else. set Num = Num + 1
    if
    {
        Num > 40
    }
    then {set A = 5}
    Squares := for. X := 1..3
    B := if{Num > 100} then {1} else {2}
    Print("{Num} {A} {Sum(array{1, 2, 3})} {B}")
