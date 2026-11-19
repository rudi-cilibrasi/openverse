# A branch started at the top level of the probe's Main, which returns at
# once. OpenVerse runs Main as the program's entry: its task ends with Main,
# which stops the branch (its defer runs), and the program ends.
# OpenVerse prints:
#   main returning | branch cleanup
# On UEFN, Main is called by the device's OnBegin (device.verse.header), so
# the branch's parent task is OnBegin's: is it cancelled when OnBegin ends,
# after "OVPROBE end" (prints: begin | main returning | end | branch cleanup),
# or does it run on (begin | main returning | end | branch tick | branch tick
# | ...)?
# Run it alone (single mode) and keep the session running for a few seconds:
# in a batch, the branch's parent is the driver's OnBegin, which goes on to
# the next probes.
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19), the probe run alone, printed
#   begin | main returning | end | branch cleanup
# and no branch tick in the 12 s after: the branch, a child of OnBegin's task,
# is stopped when OnBegin ends, as OpenVerse stops it when its Main ends.
Main()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        loop:
            Sleep(0.5)
            Print("OVPROBE branch tick")
    Print("OVPROBE main returning")
