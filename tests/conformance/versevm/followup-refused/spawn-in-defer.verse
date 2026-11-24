# Book: Tests/FlowControl/defer.versetest:1094 (1 case): spawn inside a defer
# of a function that does not suspend. The Book's tests expect it valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "spawn in a defer is not
# supported (#156)"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   body | after spawn in defer
# OpenVerse now prints it too (#724, Lean and C): a defer of a function that
# cannot suspend may spawn (tests/verse/spawn_in_defer); in a <suspends>
# function it is still refused.
Coro()<suspends>:void = {}

Main():void =
    defer:
        spawn{Coro()}
        Print("OVPROBE after spawn in defer")
    Print("OVPROBE body")
