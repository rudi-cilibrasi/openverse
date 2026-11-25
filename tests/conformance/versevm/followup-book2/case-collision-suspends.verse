# Book: Tests/Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest:67
# (bp_vm_only; :154 is the module form): two <suspends> methods whose names
# differ only in case. The Book's Blueprint VM refuses them with 9002 (their
# coroutine code collides) and 9200; no Verse VM twin. OpenVerse admits them
# and prints
#   lower 42 | upper 420
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9002 (L9) "Found existing type
# 'task_cc$Function' that is already being created this compile. Please
# rename the other to be case insensitive unique."; 9200 (L10) "Found
# multiple functions that map to the same target function. Please rename the
# function to be case insensitive unique. See:".
cc := class:
    Function()<suspends>:int = 42
    FUNCTION()<suspends>:int = 420

Main()<suspends>:void =
    Obj := cc{}
    A := Obj.Function()
    B := Obj.FUNCTION()
    Print("OVPROBE lower {A}")
    Print("OVPROBE upper {B}")
