# a class with a type parameter of its own below an interface without one
# (#276): its objects hold a value of it, and a dispatch from the interface
# opens it, as for a class whose parent's type arguments do not give it
named := interface:
    Name():string
box(t:type) := class(named):
    Value:t
    Name<override>():string = "box"
Main():void =
    N:named = box(int){Value := 3}
    Print(N.Name())
    Ns:[]named = array{N, box(string){Value := "s"}}
    for (M : Ns) { Print(M.Name()) }
