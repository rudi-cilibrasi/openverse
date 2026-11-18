# #704 follow-up: the element does not exist before the right operand, which
# appends it in place. OpenVerse checks the index when it reads the old value,
# after the right operand: "ok rows 1 row0 2". If the index is checked when
# the place is resolved, before it: "failed rows 0".
Main()<transacts>:void =
    var X:[][]int = array{}
    if (set X[0] += if (set X += array{array{5}}; 0 = 0) then array{1} else array{1}, Row := X[0]):
        Print("OVPROBE ok rows {X.Length} row0 {Row.Length}")
    else:
        Print("OVPROBE failed rows {X.Length}")
