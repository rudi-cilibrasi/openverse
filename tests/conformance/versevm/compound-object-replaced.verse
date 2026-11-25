# #704 follow-up: a variable that holds an object; the right operand replaces
# the variable. OpenVerse writes the object the place named before the right
# operand: "old 6 new 100". Reading after the right operand: "old 1 new 105".
cell := class:
    var V:int = 1

Main()<transacts>:void =
    C1 := cell{V := 1}
    var O:cell = C1
    set O.V += if (set O = cell{V := 100}; 0 = 0) then 5 else 5
    Print("OVPROBE old {C1.V} new {O.V}")
