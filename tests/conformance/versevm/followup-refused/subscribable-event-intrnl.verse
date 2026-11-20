# Book: Tests/Event.versetest 83, 117, decls;
# Tests/Bugs/SOL-8836-RepeatedInstantiation.versetest 12, decls (5 cases):
# subscribable_event_intrnl(t), subscribed and signalled (the Book's API
# reference marks it <epic_internal>). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown struct
# 'subscribable_event_intrnl'"
# If UEFN 43.12 admits it, it prints
#   seen 1
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Seen(X:int):void = Print("OVPROBE seen {X}")

Main():void =
    E := subscribable_event_intrnl(int){}
    E.Subscribe(Seen)
    E.Signal(1)
