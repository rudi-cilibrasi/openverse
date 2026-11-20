# Book: Tests/Classes/Constructor.versetest 122, 280, 648, 655 (4 cases): a
# constructor function called with <constructor> inside an archetype written
# in a function, not in a constructor's body (ch. 10, lines 272-275). The
# Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "MakeBase<constructor>(…)
# delegates to a constructor: it can only be an item of a constructor's body;
# call it as MakeBase(…)"
# If UEFN 43.12 admits it, it prints
#   label made extra 2
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
# Control: constructor-delegation-archetype-control (the delegation inside a
# constructor function's body).
base := class:
    Label:string

MakeBase<constructor>(L:string) := base:
    Label := L

derived := class(base):
    Extra:int

Main():void =
    X := derived:
        Extra := 2
        MakeBase<constructor>("made")
    Print("OVPROBE label {X.Label} extra {X.Extra}")
