# array, map, option and logic take their body as any keyword does: `{…}`, or
# `:` and an indented block (or the rest of the line), or `.` and an
# expression on its line. An array or map block separates its items with
# `,`, `;` or new lines (Book of Verse tests: `array:` and `1,2;`,
# `X:[?int]int = map:` and an entry per line, `array. 1`, `option:`).
Sum(A:[]int):int =
    var S:int = 0
    for (E : A). set S += E
    S
Main():void =
    A := array:
        42
        -13
        53, 10;
    B := array. 7
    M:[int]int = map:
        1 => 2
        3 => 4
    O := option:
        5
    if (V := O?, L := logic. 1 = 1, B0 := B[0], M3 := M[3]):
        Print("{Sum(A)} {B0} {M3} {V} {A.Length} {M.Length}")
