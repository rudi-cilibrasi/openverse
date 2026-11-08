# <suspends> methods: virtual dispatch, arms over one object, a generic class's method, spawning a method call (#156)
creature := class:
    Name:string
    var Steps:int = 0
    Walk(N:int)<suspends>:int =
        var I:int = 0
        loop:
            if (I >= N) then break
            Sleep(0.5)
            set Steps += 1
            set I += 1
        Steps
    Describe()<suspends>:string =
        Sleep(0.1)
        "a creature"
cat := class(creature):
    Describe<override>()<suspends>:string =
        Sleep(0.2)
        "the cat {Name}"
box(t:type) := class:
    V:t
    Later()<suspends>:t =
        Sleep(0.3)
        V
Main()<suspends>:void =
    C := cat{Name := "tom"}
    D := creature{Name := "rex"}
    Cs:[]creature = array{C, D}
    for (X : Cs):
        Print(X.Describe())
    R := sync:
        C.Walk(3)
        D.Walk(2)
    Print("{R(0)} {R(1)} {C.Steps}")
    B := box(int){V := 5}
    Print("{B.Later()}")
    T := spawn{C.Walk(1)}
    Print("{T.Await()}")
