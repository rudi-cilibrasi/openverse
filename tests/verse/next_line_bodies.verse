# A braced body's '{' may start the next line, at the definition's column
# (Book of Verse tests: `getArrayCount(inArr:[]int):int=` then '{' at column
# 0), and a value after '=', ':=' or '=>' that starts a later line, deeper,
# is the indented block of those lines, as a function's body is: its value
# is the last line's.
Count(A:[]int):int=
{
    var N:int = 0
    for (I : A):
        set N += 1
    N
}

M := module:
    Twice<public>(X:int):int =
    {
        2 * X
    }

c := class:
    V:int = 5
    Get():int=
    {
        V
    }

Main():void =
    Value :=
        1
        2
        3
    var W:int = 0
    set W =
        Value
        Value + 1
    X := case(10):
        10 =>
            7
            8
        _ => 9
    Y:int =
        Z := 4
        Z * Z
    Print("{Count(array{4,5,6})} {M.Twice(21)} {c{}.Get()} {Value} {W} {X} {Y}")
