# #704 follow-up: the right operand extends the variable with +=. OpenVerse
# takes set X += as a replacement of X's array, so the update goes to the
# replaced one: "rows 2 row0 3". If += appends in place: "rows 2 row0 4".
Main()<transacts>:void =
    var X:[][]int = array{array{1, 2, 3}}
    if (set X[0] += if (set X += array{array{5}}; 0 = 0) then array{42} else array{42}, Row := X[0]):
        Print("OVPROBE rows {X.Length} row0 {Row.Length}")
    else:
        Print("OVPROBE update failed")
