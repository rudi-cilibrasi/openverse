# Book: Tests/Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest:92
# (bp_vm_only), grouped with :98, :166 and :172 (a third name, other
# effects, other access specifiers): two module functions whose names differ
# only in case. The Book's Blueprint VM refuses them at link time, 9200 (its
# names are case-insensitive); the cases are bp_vm_only, so the Verse VM
# takes them, and no rule of the language refuses them. OpenVerse admits
# them and prints
#   lower 42 | upper 420
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# OpenVerse would then need a case-insensitive check of the names of one
# scope. Control: case-collision-module-fn-control (the Book's valid :106).
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9200 (L13) "Found multiple functions
# that map to the same target function. Please rename the function to be
# case insensitive unique. See:".
Function():int = 42
FUNCTION():int = 420

Main():void =
    Print("OVPROBE lower {Function()}")
    Print("OVPROBE upper {FUNCTION()}")
