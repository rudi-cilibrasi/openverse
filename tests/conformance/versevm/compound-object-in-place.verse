# #704 follow-up, controls: writes into an object's field that do not
# replace its array (an element set in place, an append, another object's
# field). OpenVerse, as reading after the right operand: "element 1 51",
# "append 1 3 7", "other object 1 3 8 9".
cell := class:
    var Arr:[]int = array{1, 2}

SetElement(C:cell)<transacts>:int =
    if (set C.Arr[1] = 50) then 1 else 1

Append(C:cell)<transacts>:int =
    set C.Arr += array{7}
    1

SetOther(Other:cell)<transacts>:int =
    set Other.Arr = array{8, 9}
    1

Main()<transacts>:void =
    C := cell{}
    if (set C.Arr[1] += SetElement(C), A := C.Arr[0], B := C.Arr[1]):
        Print("OVPROBE element {A} {B}")
    set C.Arr = array{1, 2}
    if (set C.Arr[1] += Append(C), A := C.Arr[0], B := C.Arr[1], E := C.Arr[2]):
        Print("OVPROBE append {A} {B} {E}")
    set C.Arr = array{1, 2}
    Other := cell{}
    if (set C.Arr[1] += SetOther(Other), A := C.Arr[0], B := C.Arr[1], X := Other.Arr[0], Y := Other.Arr[1]):
        Print("OVPROBE other object {A} {B} {X} {Y}")
