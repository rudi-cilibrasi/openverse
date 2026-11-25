# #704 follow-up: nested indices; the right operand replaces the variable.
# OpenVerse (the place resolved before the right operand): "row1 7 7".
# Reading the place after the right operand: "row1 17 7".
Main()<transacts>:void =
    var G:[][]int = array{array{1, 2}, array{3, 4}}
    if (set G[1][0] += if (set G = array{array{0, 0}, array{7, 7}}; 0 = 0) then 10 else 10):
        if (Row := G[1], A := Row[0], B := Row[1]):
            Print("OVPROBE row1 {A} {B}")
    else:
        Print("OVPROBE update failed")
