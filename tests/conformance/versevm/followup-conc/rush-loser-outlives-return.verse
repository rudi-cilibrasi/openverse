# A rush's arm that goes on after the rush: does it outlive the function that
# ran the rush, as the Book's AsyncContextCancellation.versetest (TEST 6,
# "arms continue until spawned function returns") says of the Verse VM?
# OpenVerse (#724) prints:
#   fast arm | function returning | returned | slow arm done | slow cleanup | after wait
# If the function's return cancelled it (the Blueprint VM's rule):
#   fast arm | function returning | slow cleanup | returned | after wait
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) printed
#   fast arm | function returning | returned | slow arm done | slow cleanup | after wait
# as OpenVerse does.
RushThenReturn()<suspends>:void =
    rush:
        block:
            Sleep(0.05)
            Print("OVPROBE fast arm")
        block:
            defer:
                Print("OVPROBE slow cleanup")
            Sleep(0.2)
            Print("OVPROBE slow arm done")
    Print("OVPROBE function returning")

Main()<suspends>:void =
    RushThenReturn()
    Print("OVPROBE returned")
    Sleep(0.4)
    Print("OVPROBE after wait")
