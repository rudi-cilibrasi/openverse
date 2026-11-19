# 3582 follow-up (#724), compile only: a module constant defined by a call
# of Sqrt, a native the Book's Runtime API reference declares
# <predicts><reads>, not <converges>. OpenVerse refuses it: "the value of
# the constant Root calls Sqrt" (3582).
Root:float = Sqrt(4.0)

Main():void =
    Print("OVPROBE root {Root}")
