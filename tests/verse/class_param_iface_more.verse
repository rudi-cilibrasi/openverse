# parametric classes below plain interfaces (#276): two interfaces, an
# interface field's default, subclasses that fix or keep the type parameter,
# a type parameter beyond the interface's (pairbox's u), generic code over
# container(t)
named := interface:
    Label:string = "?"
    Name():string
sized := interface:
    Size():int
box(t:type) := class(named, sized):
    Items:[]t
    Name<override>():string = "box of {Items.Length}"
    Size<override>():int = Items.Length
ibox := class(box(int)):
    Name<override>():string = "ibox {Items.Length}"
sbox(t:type) := class(box(t)):
    Extra:t
    Size<override>():int = Items.Length + 1
container(t:type) := interface:
    Get():t
    Count():int
pairbox(t:type, u:type) := class(container(t)):
    V:t
    W:[]u
    Get<override>():t = V
    Count<override>():int = W.Length
Show(N:named):string = "{N.Label}:{N.Name()}"
Total(Ss:[]sized):int =
    var T:int = 0
    for (S : Ss) { set T += S.Size() }
    T
First(C:container(t) where t:type):t = C.Get()
Main():void =
    B := box(string){Items := array{"a", "b"}}
    Print(Show(B))
    Print(Show(ibox{Items := array{1, 2, 3}}))
    Print(Show(sbox(logic){Items := array{true}, Extra := false}))
    Print("{Total(array{B, ibox{Items := array{1}}, sbox(int){Items := array{}, Extra := 0}})}")
    P := pairbox(int, string){V := 7, W := array{"x", "y"}}
    Print("{First(P)} {P.Count()}")
    Cs:[]container(int) = array{P, pairbox(int, logic){V := 8, W := array{}}}
    for (C : Cs) { Print("{C.Get()} {C.Count()}") }
