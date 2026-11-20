# Book: Tests/FlowControl/defer.versetest:1094 (1 case): spawn inside a defer
# of a function that does not suspend. The Book's tests expect it valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "spawn in a defer is not
# supported (#156)"
# If UEFN 43.12 admits it, it prints
#   body | after spawn in defer
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Coro()<suspends>:void = {}

Main():void =
    defer:
        spawn{Coro()}
        Print("OVPROBE after spawn in defer")
    Print("OVPROBE body")
