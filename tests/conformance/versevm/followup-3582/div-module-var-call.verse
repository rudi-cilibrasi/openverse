# 3582 follow-up (#724), compile only: a module-scoped var whose initial
# value is a call of a <computes> function, the form of the Book's ch. 16
# (`var GlobalCounter:weak_map(session, int) = map{}`) with a call in place
# of the literal. OpenVerse refuses it before the rule is reached: it has no
# `session` (its module-scoped vars are keyed by a class with
# <module_scoped_var_weak_map_key>); with such a key it refuses the call
# (3582, the module-scoped var's default).
Fresh()<computes>:weak_map(session, int) = map{}

var Scores:weak_map(session, int) = Fresh()

Main():void =
    Print("OVPROBE compiled")
