# Two tasks that both sleep zero (the next update) resume in the order they
# slept, and a third that slept in the update after resumes after both.
# Tests LANGUAGE.md, Readings, "Sleep(0.0)": "it yields ... it waits one
# tick, the next update" (settled on Epic: followup-conc/sleep-zero-next-
# update); this asks the order of tasks resuming in one update.
# OpenVerse prints (Lean and C agree):
#   first after 1 | second after 1 | third after 2 | main done
Napper(Name:string, Zeros:int)<suspends>:void =
    for (I := 1..Zeros):
        Sleep(0.0)
    Print("OVPROBE {Name} after {Zeros}")

Main()<suspends>:void =
    spawn{Napper("first", 1)}
    spawn{Napper("second", 1)}
    spawn{Napper("third", 2)}
    Sleep(0.3)
    Print("OVPROBE main done")
