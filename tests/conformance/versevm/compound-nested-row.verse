# #704 follow-up: nested indices; the right operand replaces the row the
# element is in, then (a control) another row. OpenVerse (the whole path
# resolved before the right operand): "same row 9 9", "other row 13 4".
# Only the variable resolved before it: "same row 19 9", "other row 13 4".
Main()<transacts>:void =
    var G:[][]int = array{array{1, 2}, array{3, 4}}
    if (set G[1][0] += if (set G[1] = array{9, 9}; 0 = 0) then 10 else 10):
        if (Row := G[1], A := Row[0], B := Row[1]):
            Print("OVPROBE same row {A} {B}")
    else:
        Print("OVPROBE same row update failed")
    set G = array{array{1, 2}, array{3, 4}}
    if (set G[1][0] += if (set G[0] = array{5}; 0 = 0) then 10 else 10):
        if (Row := G[1], A := Row[0], B := Row[1]):
            Print("OVPROBE other row {A} {B}")
    else:
        Print("OVPROBE other row update failed")
