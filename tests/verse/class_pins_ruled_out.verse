# dispatch through classes that fix type arguments the receiver rules out, or
# whose only classes below fix them (#142, review of #155)
box(t:type) := class:
    V:t
    Get():t = V
    Name():string = "box"
mid(t:type) := class<abstract>(box(t)):
    Get<override>():t = V
    Name<override>():string = "mid"
lb := class(mid(logic)):
    Name<override>():string = "lb"
int_mid := class(mid(int)):
    Get<override>():int = V + 1
N(B:box(t) where t:type):string = B.Name()
Main():void =
    B:box(int) = box(int){V := 1}
    Print("{B.Get()} {B.Name()}")
    Print(N(int_mid{V := 1}))
    Print(N(lb{V := true}))
    I:box(int) = int_mid{V := 4}
    Print("{I.Get()} {I.Name()}")
