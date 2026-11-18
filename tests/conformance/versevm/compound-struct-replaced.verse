# #704 follow-up: struct fields. The right operand replaces a struct
# variable: OpenVerse "struct 50" (reading after it: "struct 55"); an array
# of structs: OpenVerse "array replaced 40" ("45"); the struct in the array:
# OpenVerse "element replaced 70" ("75").
pair := struct<computes>:
    N:int = 0

Main()<transacts>:void =
    var S:pair = pair{N := 1}
    set S.N += if (set S = pair{N := 50}; 0 = 0) then 5 else 5
    Print("OVPROBE struct {S.N}")
    var Ps:[]pair = array{pair{N := 1}, pair{N := 2}}
    if (set Ps[1].N += if (set Ps = array{pair{N := 30}, pair{N := 40}}; 0 = 0) then 5 else 5, P := Ps[1]):
        Print("OVPROBE array replaced {P.N}")
    set Ps = array{pair{N := 1}, pair{N := 2}}
    if (set Ps[1].N += if (set Ps[1] = pair{N := 70}; 0 = 0) then 5 else 5, P := Ps[1]):
        Print("OVPROBE element replaced {P.N}")
