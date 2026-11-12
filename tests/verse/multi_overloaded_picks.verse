# Overloaded functions with several values (#283): the overload a call takes is the one an earlier
# elaboration found its arguments fit, by the call's place. So a function that calls only an overload
# with one value has one value itself, and may be called outside a failure context; one that calls
# an overload with several values has several; methods too (`Get` stays a method, of one value, so a
# local may be named like it). And such calls work wherever code is: in constants, class fields'
# defaults, a class block, parameters' defaults
Two(N:int):int = N * 2
Two(S:string):int = S.Length | 100
Twice(N:int):int = Two(N) + 1
Both(S:string):int = Two(S) + 1
Vals:[]int = for (X := Two("abc")) { X }
c := class:
    Ks:[]int = for (X := Two("ab")) { X }
    block:
        for (X := Both("q")) { Print("blk {X}") }
    Get(N:int):int = Two(N) + 1
    Gets(S:string):int = Two(S) + 1
F(?Xs:[]int = for (X := Two("q")) { X }):int = Xs.Length
Main():void =
    Print("a {Twice(3)}")
    Print("b {Two(4)}")
    for (X := Both("xy")) { Print("c {X}") }
    for (V : Vals) { Print("d {V}") }
    O := c{}
    for (V : O.Ks) { Print("e {V}") }
    Print("g {F()}")
    if (Y := Both("z"), Y > 50) then Print("h {Y}")
    if (Y := Twice(1) + Two("long")) then Print("i {Y}")
    Get := O.Get(4)
    Print("j {Get}")
    for (X := O.Gets("uv")) { Print("k {X}") }
