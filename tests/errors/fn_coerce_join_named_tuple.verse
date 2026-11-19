# expect: 9:45: using a value of type type{_(:string, ?Y:int = …):string} as a value of type type{_(:string):string} is not yet implemented
# the branches of an if are a function of a string and a named, defaulted
# int, and one of a string, at type{_(:string):string}: the first needs a
# wrapper (UEFN 43.12, error 3502, at the first branch only:
# followup-book2/join-named-tuple; Tuple.versetest:456, bp_vm_only).
ArrayAndNamedToString(X:string, ?Y:int = 1):string = X
ArrayToString(X:string):string = X
Pick(Flag:logic):string =
    F:type{_(:string):string} = if (Flag?) { ArrayAndNamedToString } else { ArrayToString }
    F("hello")
Main():void =
    Print(Pick(true))
