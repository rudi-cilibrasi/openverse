# Sleep with a negative duration. Epic's Verse VM and Blueprint VM yield at
# Sleep(0.0) (UEFN 43.12, vm-sleep-zero-yields), and OpenVerse now does too;
# OpenVerse still completes a negative (or NaN) duration at once, without
# yielding (docs/LANGUAGE.md, Concurrency, Time).
# OpenVerse prints:
#   worker before sleep | worker after sleep | main after spawn | main after wait
# If a negative duration yields as zero does:
#   worker before sleep | main after spawn | worker after sleep | main after wait
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) printed
#   worker before sleep | worker after sleep | main after spawn | main after wait
# as OpenVerse does: a negative duration does not yield.
Worker()<suspends>:void =
    Print("OVPROBE worker before sleep")
    Sleep(-1.0)
    Print("OVPROBE worker after sleep")

Main()<suspends>:void =
    spawn{Worker()}
    Print("OVPROBE main after spawn")
    Sleep(0.1)
    Print("OVPROBE main after wait")
