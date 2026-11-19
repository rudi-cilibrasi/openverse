# A branch started in the first arm of a sync: is it cancelled when that arm
# ends (its parent is the arm, each arm of a sync a task of its own, the
# Book's AsyncContextCancellation.versetest), or when the sync ends, or when
# the function that runs the sync returns?
# OpenVerse (#724) prints:
#   arm one done | branch cleanup | arm two done | after sync | after wait
# If it were cancelled only when the sync ends:
#   arm one done | branch tick | arm two done | branch cleanup | after sync | after wait
# If only when the function returns (the Blueprint VM's rule):
#   arm one done | branch tick | arm two done | after sync | branch tick ... | branch cleanup | after wait
Run()<suspends>:void =
    sync:
        block:
            branch:
                defer:
                    Print("OVPROBE branch cleanup")
                loop:
                    Sleep(0.1)
                    Print("OVPROBE branch tick")
            Sleep(0.05)
            Print("OVPROBE arm one done")
        block:
            Sleep(0.2)
            Print("OVPROBE arm two done")
    Print("OVPROBE after sync")
    Sleep(0.3)

Main()<suspends>:void =
    Run()
    Sleep(0.1)
    Print("OVPROBE after wait")
