# Book: Tests/Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest:5
# (bp_vm_only), grouped with :11, :73, :79, :85 and :160 (a third name,
# <decides>, other effects, other access specifiers): two methods of one
# class whose names differ only in case. The Book's Blueprint VM refuses
# them at link time, 9200; no Verse VM twin. OpenVerse admits them and
# prints
#   lower 42 | upper 420
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Control: case-collision-module-fn-control (module functions; the Book's
# :19 is its class form).
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9200 (L13) "Found multiple functions
# that map to the same target function. Please rename the function to be
# case insensitive unique. See:".
cc := class:
    Function():int = 42
    FUNCTION():int = 420

Main():void =
    Obj := cc{}
    Print("OVPROBE lower {Obj.Function()}")
    Print("OVPROBE upper {Obj.FUNCTION()}")
