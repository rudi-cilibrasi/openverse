# A branch started in the arm of a race that wins: is it cancelled when that
# arm ends (each race arm a task of its own, the Book's
# AsyncContextCancellation.versetest), before the code after the race?
# OpenVerse (#724) prints:
#   winner done | winner branch cleanup | loser cleanup | after race | after wait
# If a race arm's branch belonged to the function's task instead:
#   winner done | loser cleanup | after race | winner branch tick | ... | after wait
Run()<suspends>:void =
    race:
        block:
            branch:
                defer:
                    Print("OVPROBE winner branch cleanup")
                loop:
                    Sleep(0.1)
                    Print("OVPROBE winner branch tick")
            Sleep(0.05)
            Print("OVPROBE winner done")
        block:
            defer:
                Print("OVPROBE loser cleanup")
            Sleep(1.0)
    Print("OVPROBE after race")
    Sleep(0.3)

Main()<suspends>:void =
    Run()
    Print("OVPROBE after wait")
