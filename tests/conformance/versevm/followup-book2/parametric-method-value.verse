# Book: Tests/Bugs/FORT-592189-MaybeCoerceToTypeCrash.versetest:4
# (bp_vm_only): a method of an instance of a parametric class returned as a
# function value (MakeClosure ... .Handle), and a method (OnCallback) passed
# as a value. The Book's Blueprint VM refuses it in code generation (IR
# error 3502); the Verse VM twin (:24, asserted at :44) is valid and agrees
# in OpenVerse. Renamed here so no two names differ only in case (the Book's
# has closure and Closure, arg1 and Arg1, ...), and the closure is called
# once. OpenVerse prints
#   callback called | after test
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3502 (L26) "Using a value of type
# type{_(:tuple(p_type,c_type)->void,:c_type where
# p_type,c_type):p_type->void} as a value of type
# tuple(tuple(first_arg,second_arg)->void,s".
bound_call(p_type:type, c_type:type) := class:
    Callback:tuple(p_type, c_type)->void
    Context:c_type
    Handle(Payload:p_type):void =
        Callback(Payload, Context)

MakeClosure(Callback:tuple(p_type, c_type)->void, Context:c_type where p_type:type, c_type:type):(p_type->void) =
    return bound_call(p_type, c_type){Callback := Callback, Context := Context}.Handle

first_arg := class {}
second_arg := class {}

tester := class:
    Test():void =
        Second := second_arg{}
        Closure := MakeClosure(OnCallback, Second)
        Closure(first_arg{})

    OnCallback(First:first_arg, Second:second_arg):void =
        Print("OVPROBE callback called")

Main():void =
    tester{}.Test()
    Print("OVPROBE after test")
