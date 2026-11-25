# flattening and unflattening tuples between parameters, variants of an
# override reached through the base, the receiver evaluated once (#231)
animal := class:
    Name()<transacts>:string = "animal"
dog := class(animal):
    Name<override>()<transacts>:string = "dog"
base := class:
    Describe(A:animal)<transacts>:string = "base sees {A.Name()}"
derived := class(base):
    Describe<override>(A:animal)<transacts>:string = "derived sees {A.Name()}"
Add(X:int, Y:int)<transacts>:int = X + Y
OnPair(F:type{_(:tuple(int, int))<transacts>:int})<transacts>:int = F((3, 4))
Mk(S:string)<transacts>:base =
    Print("made {S}")
    derived{}
Check(X:int)<transacts><decides>:int = X > 0
UseD(F:type{_(:int)<transacts><decides>:int})<transacts>:int = if (V := F[5]) then V else -1
c2 := class:
    Pos(X:int)<transacts><decides>:int = X > 0
Main():void =
    # flattening: a two-parameter function at a single tuple parameter
    Print("{OnPair(Add)}")
    # an override's implementation through the base's variant value
    B:base = derived{}
    G:type{_(:dog)<transacts>:string} = B.Describe
    Print(G(dog{}))
    # the receiver is evaluated once, when the value is made
    H:type{_(:dog)<transacts>:string} = Mk("once").Describe
    Print(H(dog{}))
    Print(H(dog{}))
    # decides methods by variance (int param stays; effects within)
    O := c2{}
    Print("{UseD(O.Pos)}")
