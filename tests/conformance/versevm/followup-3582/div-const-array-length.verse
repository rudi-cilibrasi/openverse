# 3582 follow-up (#724), compile only: a module constant defined by an
# array's Length, which the Book's Runtime API reference declares
# <converges>. OpenVerse admits it and prints "count 3".
Items:[]int = array{1, 2, 3}
Count:int = Items.Length

Main():void =
    Print("OVPROBE count {Count}")
