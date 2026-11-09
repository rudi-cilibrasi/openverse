# expect: pair has type parameters that base does not have, which would be unknown here: a cast opens them only as the first clause of an if's condition
base(t:type) := class:
    Value:t
pair(t:type, u:type) := class(base(t)):
    Other:u
Main():void =
    B:base(int) = pair(int, string){Value := 1, Other := "o"}
    X := option{pair[B]}
    if (X?) then Print("pair")
