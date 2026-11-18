# #704 follow-up: rows in an object's field. The right operand replaces the
# element's row, another row, or the whole field. OpenVerse: "same row 9 9",
# "other row 13 4", "field 7 7". Reading after the right operand: "same row
# 19 9", "other row 13 4", "field 17 7".
cell := class:
    var Grid:[][]int = array{array{1, 2}, array{3, 4}}

Main()<transacts>:void =
    C := cell{}
    if (set C.Grid[1][0] += if (set C.Grid[1] = array{9, 9}; 0 = 0) then 10 else 10, Row := C.Grid[1], A := Row[0], B := Row[1]):
        Print("OVPROBE same row {A} {B}")
    set C.Grid = array{array{1, 2}, array{3, 4}}
    if (set C.Grid[1][0] += if (set C.Grid[0] = array{5}; 0 = 0) then 10 else 10, Row := C.Grid[1], A := Row[0], B := Row[1]):
        Print("OVPROBE other row {A} {B}")
    set C.Grid = array{array{1, 2}, array{3, 4}}
    if (set C.Grid[1][0] += if (set C.Grid = array{array{0}, array{7, 7}}; 0 = 0) then 10 else 10, Row := C.Grid[1], A := Row[0], B := Row[1]):
        Print("OVPROBE field {A} {B}")
