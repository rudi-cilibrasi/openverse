# Book: Tests/Effects.versetest 304, 305; Tests/ParametricTypes.versetest:375
# (3 cases): <converges> on an abstract method, which has no body (the Book's
# cases also put it in a function type and on a parametric class; UEFN 43.12
# refuses it on a function with a body, 3565,
# followup-3582/div-const-converges). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "<converges> is unsupported:
# termination contracts are not checked (#494); execution fuel is not a
# termination proof"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   compiled
# OpenVerse now prints it too (#724, Lean and C): <converges> is admitted on
# a method without a body (tests/verse/converges_abstract), and still
# refused on a function with a body, as Epic refuses it (3565).
shape := class<abstract>:
    Area()<converges>:int

Main():void =
    Print("OVPROBE compiled")
