# #704 follow-up: a map's entry; the right operand replaces the map.
# OpenVerse: "entry 100 size 1". Reading after the right operand:
# "entry 101 size 1".
Main()<transacts>:void =
    var M:[int]int = map{1 => 10, 2 => 20}
    if (set M[1] += if (set M = map{1 => 100}; 0 = 0) then 1 else 1):
        if (V := M[1]):
            Print("OVPROBE entry {V} size {M.Length}")
    else:
        Print("OVPROBE update failed")
