# 3582 follow-up (#724), compile only: a module constant defined by a call
# of Quotient, a native the Book's Runtime API reference declares
# <computes><predicts><decides>, not <converges>. OpenVerse refuses it:
# "the value of the constant Half calls Quotient" (3582).
Half:int = Quotient[7, 2] or 0

Main():void =
    Print("OVPROBE half {Half}")
