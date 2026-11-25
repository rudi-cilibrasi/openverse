# Three spawned tasks with sleeps 0.3 s apart finish in the order of their
# durations, not of their spawning.
# Tests LANGUAGE.md, Readings, "Sleep(S) rounding": "the first tick at or
# after the deadline"; only the order is compared, not the ticks.
# OpenVerse prints (Lean and C agree):
#   all spawned | woke short | woke middle | woke long | main done
Napper(Name:string, D:float)<suspends>:void =
    Sleep(D)
    Print("OVPROBE woke {Name}")

Main()<suspends>:void =
    spawn{Napper("long", 0.9)}
    spawn{Napper("short", 0.3)}
    spawn{Napper("middle", 0.6)}
    Print("OVPROBE all spawned")
    Sleep(1.2)
    Print("OVPROBE main done")
