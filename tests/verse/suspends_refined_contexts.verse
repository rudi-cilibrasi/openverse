# refined immediate calls and interface fields in a suspends function: operands, loops, race arms, defers (#179)
box(t:type) := class:
    var V:t
    Size():int = 0
    Peek():t = V
int_box := class(box(int)):
    Size<override>():int = V
    Peek<override>():int = V * 10
holder(t:type) := interface:
    var Item:t
intbox := class(holder(int)):
    N:int = 0
strbox := class(holder(string)):
    S:string = "s"
G(B:box(t), X:t where t:type)<suspends>:t =
    defer:
        Print("G size {B.Size()}")
    Sleep(0.1)
    var R:t = X
    N := B.Size() + 1
    for (I := 1..2):
        Sleep(0.1)
        set R = B.Peek()
    W := race:
        block:
            Sleep(0.1)
            B.Peek()
        block:
            Sleep(1.0)
            X
    Print("n={N} {B.Size()}")
    R
H(H:holder(t), X:t where t:type)<suspends>:t =
    Sleep(0.1)
    set H.Item = X
    Sleep(0.1)
    H.Item
Main()<suspends>:void =
    Print("{G(int_box{V := 4}, 0)}")
    Print("{G(box(string){V := "q"}, "x")}")
    Print("{H(intbox{Item := 1}, 7)} {H(strbox{Item := "a"}, "b")}")
