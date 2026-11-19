# Book: Tests/Bugs/SOL-5477-CrashInGenClassDefinition.versetest:5
# (bp_vm_only): a parametric interface whose method takes a function of the
# type parameter, F(G(:t):void), implemented by a class of a(int). The
# Book's Blueprint VM refuses it in code generation (IR error 3502); the
# Verse VM twin (:13, asserted at :21) is valid and agrees in OpenVerse,
# which prints
#   called
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Control: interface-fn-param-generic-control (the same with F(X:t)).
TheG(X:int):void = {}

a(t:type) := interface:
    F(G(:t):void)<transacts>:void

b := class(a(int)):
    F<override>(G(:int):void)<transacts>:void = {}

Main():void =
    Obj:b = b{}
    Obj.F(TheG)
    Print("OVPROBE called")
