# expect: cannot cast a base(int) to pair here: the cast opens pair's type argument u for the code after it, outside which its value, a pair(int, u'), would name what is unknown (#250)
base(t:type) := class:
    Value:t
pair(t:type, u:type) := class(base(t)):
    Other:u
Main():void =
    B:base(int) = pair(int, string){Value := 1, Other := "o"}
    X := option{pair[B]}
    if (X?) then Print("pair")
