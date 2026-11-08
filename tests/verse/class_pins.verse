# overrides in a class that fixes its parent's type argument (#142)
box(t:type) := class:
    var V:t
    Get():t = V
    Put(X:t):void =
        set V = X
int_box := class(box(int)):
    Get<override>():int = V + 1
    Put<override>(X:int):void =
        set V = X * 10
GetAny(B:box(t) where t:type):t = B.Get()
PutAny(B:box(t), X:t where t:type):void = B.Put(X)
Main():void =
    I := int_box{V := 41}
    Print("{GetAny(I)}")
    Print("{GetAny(box(int){V := 7})}")
    Print(GetAny(box(string){V := "s"}))
    PutAny(I, 5)
    Print("{I.V} {GetAny(I)}")
    B:box(int) = I
    Print("{B.Get()}")
    S := box(string){V := "a"}
    PutAny(S, "b")
    Print(S.Get())
