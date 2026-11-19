# A spawned task that ends with two child branches, each started in a
# helper that returned: after the task's own defer (branch-in-branch, UEFN
# 43.12), which child is stopped first?
# OpenVerse (#724) stops a task's children newest first.
# OpenVerse prints:
#   runner ending | runner cleanup | second cleanup | first cleanup | after wait
# If the oldest were stopped first:
#   runner ending | runner cleanup | first cleanup | second cleanup | after wait
First()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE first cleanup")
        Sleep(10.0)

Second()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE second cleanup")
        Sleep(10.0)

Runner()<suspends>:void =
    defer:
        Print("OVPROBE runner cleanup")
    First()
    Second()
    Sleep(0.1)
    Print("OVPROBE runner ending")

Main()<suspends>:void =
    spawn{Runner()}
    Sleep(0.3)
    Print("OVPROBE after wait")
