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
Main()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        loop:
            Sleep(0.5)
            Print("OVPROBE branch tick")
    Print("OVPROBE main returning")
