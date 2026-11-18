# #704 follow-up: an array in a generic class's field and in an interface's
# field, replaced by the right operand. OpenVerse: "generic 40", "interface 8
# 9". Reading after the right operand: "generic 41", "interface 8 10".
box(t:type) := class:
    var Items:[]t = array{}

holder := interface:
    var Vals:[]int

impl := class(holder):
    var Vals<override>:[]int = array{1, 2}

Main()<transacts>:void =
    Bx := box(int){Items := array{1, 2}}
    if (set Bx.Items[0] += if (set Bx.Items = array{40}; 0 = 0) then 1 else 1, X := Bx.Items[0]):
        Print("OVPROBE generic {X}")
    I:holder = impl{}
    if (set I.Vals[1] += if (set I.Vals = array{8, 9}; 0 = 0) then 1 else 1, A := I.Vals[0], B := I.Vals[1]):
        Print("OVPROBE interface {A} {B}")
