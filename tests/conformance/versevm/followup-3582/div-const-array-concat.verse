# 3582 follow-up (#724), compile only: a module constant defined by the
# concatenation of two arrays; the Book's Runtime API reference declares
# operator'+'(Lhs:[]t, Rhs:[]t)<converges>. OpenVerse admits it and prints
# "length 2".
Both:[]int = array{1} + array{2}

Main():void =
    Print("OVPROBE length {Both.Length}")
