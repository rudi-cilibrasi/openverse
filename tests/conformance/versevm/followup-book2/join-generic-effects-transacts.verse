# Book: Tests/Function.versetest:271 (bp_vm_only): the join of
# DecidesIdentity <computes><decides> and TransactsIdentity <transacts>,
# both generic, at type{_(:int)<decides><transacts>:int}. The Book's
# Blueprint VM refuses it in code generation (IR error 3502, twice); the
# Verse VM twin (:281) is valid and agrees in OpenVerse, which prints
#   true branch 1 | false branch 1
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Control: join-generic-effects-transacts-control (TransactsIdentity alone,
# the Book's :231).
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3502 (L14) "Using a value of type
# type{_(:int)<computes><decides>:int} as a value of type
# type{_(:int)<transacts><decides>:int} is not yet implemented."; 3502 (L14)
# "Using a value of type type{_(:int)<transacts>:int} as a value of type
# type{_(:int)<transacts><decides>:int} is not yet implemented.".
DecidesIdentity(X:t where t:type)<computes><decides>:t = X
TransactsIdentity(X:t where t:type)<transacts>:t = X

Pick(Flag:logic)<transacts><decides>:int =
    F:type{_(:int)<decides><transacts>:int} = if (Flag?) { DecidesIdentity } else { TransactsIdentity }
    F[1]

Main():void =
    if (V := Pick[true]):
        Print("OVPROBE true branch {V}")
    if (V := Pick[false]):
        Print("OVPROBE false branch {V}")
