# expect: using a value of type type{_(:type{_(?A:int):int}):int} as a value of type type{_(:type{_(?A:int = …, ?B:int = …):int}):int} is not yet implemented
# the branches of an if are F1(F(?A:int):int) and F3(F(?B:int):int) at
# type{_(G(?A:int = 0, ?B:int = 0):int):int}: a parameter of each is a
# function type of other named parameters, which needs a wrapper (UEFN 43.12,
# error 3502: followup-book2/join-named-default-param; DefaultNamed.versetest
# 741, 751, bp_vm_only).
F1(F(?A:int):int):int = F(?A := 1)
F3(F(?B:int):int):int = F(?B := 3)
F9(?A:int = 9, ?B:int = 10):int = A + B
Pick(Flag:logic):int =
    F:type{_(G(?A:int = 0, ?B:int = 0):int):int} = if (Flag?) { F1 } else { F3 }
    F(F9)
Main():void =
    Print("{Pick(true)}")
