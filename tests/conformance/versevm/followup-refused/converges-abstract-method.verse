# Book: Tests/Effects.versetest 304, 305; Tests/ParametricTypes.versetest:375
# (3 cases): <converges> on an abstract method, which has no body (the Book's
# cases also put it in a function type and on a parametric class; UEFN 43.12
# refuses it on a function with a body, 3565,
# followup-3582/div-const-converges). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "<converges> is unsupported:
# termination contracts are not checked (#494); execution fuel is not a
# termination proof"
# If UEFN 43.12 admits it, it prints
#   compiled
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
shape := class<abstract>:
    Area()<converges>:int

Main():void =
    Print("OVPROBE compiled")
