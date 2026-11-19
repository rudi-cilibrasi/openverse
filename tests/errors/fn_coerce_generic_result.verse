# expect: the result of MakeClosure, type{_(:p_type):void}, has its type parameter p_type inside a function type
# MakeClosure, generic, returns p_type->void, its type parameter inside a
# function type: called at p_type = first_arg, the function it returns needs a
# wrapper, which Epic's Verse compiler does not make (UEFN 43.12, error 3502:
# followup-book2/parametric-method-value; the Book of Verse's
# FORT-592189-MaybeCoerceToTypeCrash.versetest:4, bp_vm_only).
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
        Print("callback called")
Main():void =
    tester{}.Test()
