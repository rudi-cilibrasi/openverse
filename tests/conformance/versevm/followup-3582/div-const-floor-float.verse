# 3582 follow-up (#724), compile only: a module constant defined by Floor of
# a float, a native the Book's Runtime API reference declares
# <reads><predicts><decides>, not <converges> (Floor of a rational is, and
# UEFN 43.12 admitted it in div-const-operator). OpenVerse refuses it: "the
# value of the constant Limit calls Floor of a float" (3582).
Limit:int = Floor[2.5] or 0

Main():void =
    Print("OVPROBE limit {Limit}")
