# any (#138): unrelated types join at any, any(X) evaluates X, and an any is opaque
GetValue(UseNumber:logic):any = if (UseNumber?) then 42 else "text"
Keep(X:t where t:type):t = X
Main():void =
    var Count:int = 0
    V := if (Count = 0) then 1 else "one"
    A := array{15.61, "Message", 3}
    B:[]any = array{1, "x"}
    Print("{A.Length} {B.Length}")
    X:any = any(42)
    Y := GetValue(true)
    Z := Keep(Y)
    W:any = block:
        set Count += 1
        "side effect"
    Print("{Count}")
