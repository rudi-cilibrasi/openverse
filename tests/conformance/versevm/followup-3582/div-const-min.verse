# 3582 follow-up (#724), compile only: a module constant defined by a call
# of Min alone, which the Book's Runtime API reference does not list (not a
# native, so not <converges>). OpenVerse refuses it: "the value of the
# constant Limit calls Min, which might not complete" (3582).
Limit:int = Min(3, 7)

Main():void =
    Print("OVPROBE limit {Limit}")
