# Book: Tests/DefaultNamed.versetest:629 and :640 (bp_vm_only): the join of
# two functions whose only parameter is named and defaulted, ?A and ?B, at
# type{_():int}. The Book's Blueprint VM refuses it in code generation (IR
# error 3502, twice); the Verse VM twins (:653, :664 assert_valid, :678,
# :682 F() = 2 and F() = 4) are valid and agree in OpenVerse, which prints
#   true branch 2 | false branch 4
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Control: join-named-default-fn-control (one such function, no join).
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3502 (L13) "Using a value of type
# (?A:int = ...)->int as a value of type tuple()->int is not yet
# implemented."; 3502 (L13) "Using a value of type (?B:int = ...)->int as a
# value of type tuple()->int is not yet implemented.".
F2(?A:int = 2):int = A
F4(?B:int = 4):int = B

Pick(Flag:logic):int =
    F:type{_():int} = if (Flag?) { F2 } else { F4 }
    F()

Main():void =
    Print("OVPROBE true branch {Pick(true)}")
    Print("OVPROBE false branch {Pick(false)}")
