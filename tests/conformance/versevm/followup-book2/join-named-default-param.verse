# Book: Tests/DefaultNamed.versetest:741 and :751 (bp_vm_only): the join of
# F1(F(?A:int):int) and F3(F(?B:int):int) at type{_(G(?A:int = 0, ?B:int =
# 0):int):int}, called with F9(?A:int = 9, ?B:int = 10). The Book's
# Blueprint VM refuses it in code generation (IR error 3502, twice); the
# Verse VM twins (:764, :768) expect 1 + 10 and 9 + 3 and agree in
# OpenVerse, which prints
#   true branch 11 | false branch 12
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Control: join-named-default-param-control (F1(F9) called, no join).
F1(F(?A:int):int):int = F(?A := 1)
F3(F(?B:int):int):int = F(?B := 3)
F9(?A:int = 9, ?B:int = 10):int = A + B

Pick(Flag:logic):int =
    F:type{_(G(?A:int = 0, ?B:int = 0):int):int} = if (Flag?) { F1 } else { F3 }
    F(F9)

Main():void =
    Print("OVPROBE true branch {Pick(true)}")
    Print("OVPROBE false branch {Pick(false)}")
