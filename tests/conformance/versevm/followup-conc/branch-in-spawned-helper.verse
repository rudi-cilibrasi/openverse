# A branch started in a helper function called by a spawned task's code: is
# its parent the spawned task (it outlives the helper, and is cancelled when
# the spawned task ends), as Epic's statement "branch runs until its parent
# task ends" and the Book's AsyncContextCancellation.versetest suggest?
# OpenVerse (#724) prints:
#   helper returning | runner after helper | branch tick | runner ending |
#   branch cleanup | main after wait
# If the branch outlived the spawned task (its parent Main, or no parent):
#   ... | runner ending | branch tick | branch tick | ... (no cleanup before
#   main after wait)
# If it were cancelled when the helper returns (the Blueprint VM's rule):
#   helper returning | branch cleanup | runner after helper | runner ending |
#   main after wait
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) printed
#   helper returning | runner after helper | branch tick | runner ending |
#   branch cleanup | main after wait
# as OpenVerse does.
Helper()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        loop:
            Sleep(0.1)
            Print("OVPROBE branch tick")
    Print("OVPROBE helper returning")

Runner()<suspends>:void =
    Helper()
    Print("OVPROBE runner after helper")
    Sleep(0.15)
    Print("OVPROBE runner ending")

Main()<suspends>:void =
    spawn{Runner()}
    Sleep(0.5)
    Print("OVPROBE main after wait")
