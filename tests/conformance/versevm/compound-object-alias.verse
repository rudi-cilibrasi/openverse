# #704 follow-up: an array in an object's field, replaced through another
# name for the object. OpenVerse watches the field through any reference:
# "alias 8 9". Seeing only the name the update writes: "alias 8 10".
cell := class:
    var Arr:[]int = array{1, 2}

Main()<transacts>:void =
    C := cell{}
    D := C
    if (set C.Arr[1] += if (set D.Arr = array{8, 9}; 0 = 0) then 1 else 1, A := C.Arr[0], B := C.Arr[1]):
        Print("OVPROBE alias {A} {B}")
    else:
        Print("OVPROBE update failed")
