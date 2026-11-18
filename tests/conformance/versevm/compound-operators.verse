# #704 follow-up: the other operators; the right operand replaces the array.
# OpenVerse: "minus 100", "times 200", "float times 4", "float divide 8".
# Reading after the right operand: "minus 99", "times 400", "float times 8",
# "float divide 4".
Main()<transacts>:void =
    var Is:[]int = array{10}
    if (set Is[0] -= if (set Is = array{100}; 0 = 0) then 1 else 1, I := Is[0]):
        Print("OVPROBE minus {I}")
    if (set Is[0] *= if (set Is = array{200}; 0 = 0) then 2 else 2, I := Is[0]):
        Print("OVPROBE times {I}")
    var Fs:[]float = array{1.5}
    if (set Fs[0] *= if (set Fs = array{4.0}; 0 = 0) then 2.0 else 2.0, F := Fs[0]):
        if (F = 4.0) then Print("OVPROBE float times 4")
        else if (F = 8.0) then Print("OVPROBE float times 8")
        else Print("OVPROBE float times other")
    if (set Fs[0] /= if (set Fs = array{8.0}; 0 = 0) then 2.0 else 2.0, F := Fs[0]):
        if (F = 8.0) then Print("OVPROBE float divide 8")
        else if (F = 4.0) then Print("OVPROBE float divide 4")
        else Print("OVPROBE float divide other")
