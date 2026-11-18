# #704 follow-up: an array in an object's field; the right operand replaces
# the field's array. OpenVerse reads the field after the right operand:
# "field 8 10". If the VerseVM resolves the field's array before it, as it
# does a variable's: "field 8 9".
cell := class:
    var Arr:[]int = array{1, 2}

Main()<transacts>:void =
    C := cell{}
    if (set C.Arr[1] += if (set C.Arr = array{8, 9}; 0 = 0) then 1 else 1, A := C.Arr[0], B := C.Arr[1]):
        Print("OVPROBE field {A} {B}")
    else:
        Print("OVPROBE update failed")
