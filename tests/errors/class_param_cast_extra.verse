# expect: pair has type parameters that base does not have, which would be unknown
base(t:type) := class:
    Value:t
pair(t:type, u:type) := class(base(t)):
    Other:u
Main():void =
    B:base(int) = pair(int, string){Value := 1, Other := "o"}
    if (P := pair[B]) then Print("no")
