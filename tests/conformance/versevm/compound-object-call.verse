# #704 follow-up: an array in an object's field, replaced inside a called
# function. OpenVerse: "call 8 9". Seeing only the right operand's own
# writes: "call 8 10".
cell := class:
    var Arr:[]int = array{1, 2}

ReplaceThenOne(C:cell)<transacts>:int =
    set C.Arr = array{8, 9}
    1

Main()<transacts>:void =
    C := cell{}
    if (set C.Arr[1] += ReplaceThenOne(C), A := C.Arr[0], B := C.Arr[1]):
        Print("OVPROBE call {A} {B}")
    else:
        Print("OVPROBE update failed")
