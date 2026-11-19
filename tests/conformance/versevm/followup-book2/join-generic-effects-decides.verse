# Book: Tests/Function.versetest:238 (bp_vm_only): the join of two generic
# functions, Identity <computes> and DecidesIdentity <computes><decides>, at
# type{_(:int)<computes><decides>:int}. The Book's Blueprint VM refuses it
# in code generation (IR error 3502); the Verse VM twin (:249) is valid and
# agrees in OpenVerse, which prints
#   true branch 1 | false branch 1
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Control: join-generic-effects-decides-control (Identity alone, the Book's
# :217).
Identity(X:t where t:type)<computes>:t = X
DecidesIdentity(X:t where t:type)<computes><decides>:t = X

Pick(Flag:logic)<computes><decides>:int =
    F:type{_(:int)<computes><decides>:int} = if (Flag?) { Identity } else { DecidesIdentity }
    F[1]

Main():void =
    if (V := Pick[true]):
        Print("OVPROBE true branch {V}")
    if (V := Pick[false]):
        Print("OVPROBE false branch {V}")
