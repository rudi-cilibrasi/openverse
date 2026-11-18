# #704 follow-up: the replaced array and its replacement differ in length.
# OpenVerse: the replaced array has no row 0, so the update fails and is
# undone, "short failed 0"; it has row 0 and its replacement none, so the
# update succeeds, "long ok 0". Reading after the right operand: "short ok 1",
# "long failed 1".
Main()<transacts>:void =
    var Short:[][]int = array{}
    if (set Short[0] += if (set Short = array{array{0}}; 0 = 0) then array{42} else array{42}):
        Print("OVPROBE short ok {Short.Length}")
    else:
        Print("OVPROBE short failed {Short.Length}")
    var Long:[][]int = array{array{1}}
    if (set Long[0] += if (set Long = array{}; 0 = 0) then array{42} else array{42}):
        Print("OVPROBE long ok {Long.Length}")
    else:
        Print("OVPROBE long failed {Long.Length}")
