# a subclass that implements an interface giving it fewer type arguments than
# its parent class's: the root counts against the interface with the fewest
# anywhere below it, so its own overrides read the type parameter from the
# receiver too (#209)
shower := interface:
    Label:string = "?"
    Show():string
container(t:type) := interface:
    Get():t
    Count():int
box(t:type) := class(container(t)):
    First:t
    Items:[]t
    Get<override>():t = First
    Count<override>():int = Items.Length
sbox(t:type) := class(box(t), shower):
    Show<override>():string =
        X:t = Get()
        Ys:[]t = array{X, X}
        "sbox {Count()} {Ys.Length}"
ibox := class(sbox(int)):
    Show<override>():string = "ibox {Get()}"
base(t:type) := class:
    V:t
    Twice():[]t = array{V, V}
child(t:type) := class(base(t), shower):
    Show<override>():string = "child {Twice().Length}"
job := interface:
    Run()<suspends>:int
wbase(t:type) := class:
    Xs:[]t
    Run2()<suspends>:int =
        Sleep(0.1)
        Xs.Length
wchild(t:type) := class(wbase(t), job):
    Run<override>()<suspends>:int = Run2() + 100
Main()<suspends>:void =
    Ss:[]shower = array{sbox(string){First := "a", Items := array{"a", "b"}}, ibox{First := 7, Items := array{7}}, child(logic){V := true}}
    for (S : Ss) { Print("{S.Label} {S.Show()}") }
    Cs:[]container(int) = array{sbox(int){First := 1, Items := array{1, 2, 3}}, box(int){First := 9, Items := array{9}}}
    for (C : Cs) { Print("{C.Count()}") }
    J:job = wchild(string){Xs := array{"x"}}
    Print("{J.Run()}")
