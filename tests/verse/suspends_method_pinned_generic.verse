# suspends methods dispatched to classes that fix some type arguments and
# keep others, or whose override has a type parameter of its own (#171)
pair(a:type, b:type) := class:
    A:a
    B:b
    First()<suspends>:a = A
    Both(X:b)<suspends>:tuple(a, b) = (A, X)
ipair(b:type) := class(pair(int, b)):
    First<override>()<suspends>:int =
        defer:
            Print("ipair first done")
        Sleep(0.5)
        A + 1
    Both<override>(X:b)<suspends>:tuple(int, b) =
        Sleep(0.2)
        (A * 10, X)
cell := class:
    N:int
box(t:type) := class:
    V:t
    Pair(X:u where u:type)<suspends>:tuple(t, u) = (V, X)
    Make()<suspends>:cell = cell{N := 0}
int_box := class(box(int)):
    Pair<override>(X:u where u:type)<suspends>:tuple(int, u) =
        Sleep(0.3)
        (V + 1, X)
    Make<override>()<suspends>:cell =
        Sleep(0.1)
        cell{N := V}
G(P:pair(a, b), Y:b where a:type, b:type)<suspends>:a =
    Q := P.Both(Y)
    P.First()
Race(P:pair(a, b), X:a where a:type, b:type)<suspends>:a =
    race:
        P.First()
        block:
            Sleep(0.2)
            X
H(B:box(t) where t:type)<suspends>:t =
    P := B.Pair("s")
    P(0)
M(B:box(t) where t:type)<suspends>:int = B.Make().N
Main()<suspends>:void =
    Print("{G(ipair(string){A := 1, B := "x"}, "y")}")
    Print("{G(pair(float, int){A := 2.5, B := 1}, 3)}")
    Print("{Race(ipair(logic){A := 7, B := true}, 99)}")
    var I:int = 0
    loop:
        if (I = 3) then break
        Print("{H(int_box{V := I})} {M(int_box{V := I * 2})}")
        set I += 1
    Print("{H(box(string){V := "q"})} {M(box(string){V := "q"})}")
