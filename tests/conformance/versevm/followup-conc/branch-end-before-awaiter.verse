# A spawned task that ends with a branch still running (started in a helper
# that returned), awaited by Main: does its child's cleanup run before Main's
# Await resumes, or after?
# OpenVerse (#724) prints (the children are stopped when the task's code
# ends, before its result is published):
#   runner ending | branch cleanup | awaited 5 | after wait
# If awaiters were resumed first:
#   runner ending | awaited 5 | branch cleanup | after wait
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) printed
#   runner ending | branch cleanup | awaited 5 | after wait
# as OpenVerse does.
Helper()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        Sleep(10.0)

Runner()<suspends>:int =
    Helper()
    Sleep(0.1)
    Print("OVPROBE runner ending")
    5

Main()<suspends>:void =
    T := spawn{Runner()}
    V := T.Await()
    Print("OVPROBE awaited {V}")
    Sleep(0.1)
    Print("OVPROBE after wait")
