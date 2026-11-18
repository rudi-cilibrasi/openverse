# Sleep(0.0): the Book's API reference says it resumes on the next update and
# always yields; its tested chapter 14 examples have it complete at once
# (OpenVerse follows the examples: docs/LANGUAGE.md, Readings).
Worker()<suspends>:void =
    Print("OVPROBE worker before sleep")
    Sleep(0.0)
    Print("OVPROBE worker after sleep")

Main()<suspends>:void =
    spawn{Worker()}
    Print("OVPROBE main after spawn")
    Sleep(0.1)
    Print("OVPROBE main after wait")
