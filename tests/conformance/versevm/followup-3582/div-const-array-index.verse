# 3582 follow-up (#724), compile only: a module constant defined by indexing
# an array, with a default for the failure; the Book's Runtime API reference
# declares operator'()'(Array:[]t, Index:int)<converges><decides>. OpenVerse
# admits it and prints "first 4".
Items:[]int = array{4, 5}
First:int = Items[0] or 0

Main():void =
    Print("OVPROBE first {First}")
