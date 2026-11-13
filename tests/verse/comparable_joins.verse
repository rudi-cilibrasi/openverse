# Joins at comparable (Book of Verse ch. 1, 1276: array{1, "two", 3.0}'s
# element type is comparable, "their common supertype"; ch. 14: widened "all
# the way to comparable"): two comparable types with nothing else in common
# join at comparable, also inside containers ([int]int and [int]float at
# [int]comparable, Tests/Operators/LogicalOr.versetest 115), and beside a
# comparable ([]int + []comparable, Tests/Operators/BinaryAddArray.versetest
# 87). Each result is y (holds) or n (fails).
c := class{}
F13(O1:?int, O2:?float)<transacts>:?[int]comparable =
    Result := option{map{0 => O1?} or map{1 => O2?}}
    return Result
Show(B:logic):string = if (B?) then "y" else "n"
Main():void =
    var CA:[]comparable = array{'a', 'b'}
    set CA = array{1, 2} + CA
    Print("{Show(logic{CA = array{1, 2, 'a', 'b'}})} {CA.Length}")
    Print("{Show(logic{F13(option{1}, false)? = map{0 => 1}})} {Show(logic{F13(false, option{2.0})? = map{1 => 2.0}})} {Show(logic{F13(false, false)?})}")
    N := array{array{1}, array{"a"}}
    Print("{Show(logic{N[1] = array{"a"}})} {Show(logic{N[0] = array{1.0}})}")
    var Count:int = 0
    V := if (Count = 0) then 1 else "one"
    W := if (Count = 1) then 1 else "one"
    Print("{Show(logic{V = 1})} {Show(logic{W = "one"})}")
    T := if (Count = 0) then (1, "a") else (2.0, "b")
    Print("{Show(logic{T = (1, "a")})} {Show(logic{T = (1.0, "a")})}")
    # (a value of a class that is not <unique> still joins at any)
    A := if (Count = 0) then 1 else c{}
    X := if (Count = 0) then false else option{4}
    if (Y := X?) then Print("{Y}") else Print("none")
