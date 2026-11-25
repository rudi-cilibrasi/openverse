# #704 controls for compound-indexed-write. A later failure undoes the update
# and the right operand's replacement: "rolled back 3" in any reading. The
# index runs once: "index calls 1". The update's value is the new row, from
# the replaced array as the right operand left it: OpenVerse "value 5 rows
# 1 row0 1"; reading after the right operand: "value 0 rows 1 row0 2".
counter := class:
    var N:int = 0

Index(C:counter, I:int)<transacts>:int =
    set C.N += 1
    I

Main()<transacts>:void =
    var R:[][]int = array{array{1, 2, 3}}
    if (set R[0] += if (set R = array{array{0}}; 0 = 0) then array{42} else array{42}, R.Length = 5):
        Print("OVPROBE unreachable")
    if (Row := R[0]):
        Print("OVPROBE rolled back {Row.Length}")
    C := counter{}
    var X:[][]int = array{array{1, 2, 3}}
    if (set X[Index(C, 0)] += if (set X = array{array{0}}; 0 = 0) then array{42} else array{42}):
        Print("OVPROBE index calls {C.N}")
    var P:[][]int = array{array{1}}
    if (V := (set P[0] += (set P[0] = array{5}; set P = array{array{0}}; array{42})), First := V[0], Row := P[0]):
        Print("OVPROBE value {First} rows {P.Length} row0 {Row.Length}")
    else:
        Print("OVPROBE update failed")
