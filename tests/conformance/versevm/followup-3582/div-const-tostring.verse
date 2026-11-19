# 3582 follow-up (#724), compile only: a module constant defined by a call
# of ToString of an int, a native the Book's Runtime API reference declares
# <computes><predicts>, not <converges>. OpenVerse refuses it: "the value
# of the constant Text calls ToString" (3582).
Text:string = ToString(42)

Main():void =
    Print("OVPROBE text {Text}")
