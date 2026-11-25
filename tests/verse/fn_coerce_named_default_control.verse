# (#724) F2, whose only parameter is named and defaulted, named where a
# type{_():int} is expected: Epic's Verse compiler makes the wrapper for a
# function named so (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086:
# admitted, followup-book2/join-named-default-fn-control; the Book of Verse's
# FORT-744399-DefaultTupleFieldsCrashComplier.versetest:36). As a branch of an
# if it is refused (errors/fn_coerce_join_named_default).
F2(?A:int = 2):int = A
F1(F(?A:int):int):int = F(?A := 1)
F9(?A:int = 9, ?B:int = 10):int = A + B
ArrayAndNamedToString(X:string, ?Y:int = 1):string = X
Main():void =
    F:type{_():int} = F2
    G:type{_(:string):string} = ArrayAndNamedToString
    Print("{F()} {F1(F9)} {G("hello")}")
