# flattening and unflattening tuples between parameters, variants of an
# override reached through the base, the receiver evaluated once (#231)
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
base := class:
    Describe(A:animal):string = "base sees {A.Name()}"
derived := class(base):
    Describe<override>(A:animal):string = "derived sees {A.Name()}"
Add(X:int, Y:int):int = X + Y
OnPair(F:type{_(:tuple(int, int)):int}):int = F((3, 4))
Mk(S:string):base =
    Print("made {S}")
    derived{}
Check(X:int)<decides>:int = X > 0
UseD(F:type{_(:int)<decides>:int}):int = if (V := F[5]) then V else -1
c2 := class:
    Pos(X:int)<decides>:int = X > 0
Main():void =
    # flattening: a two-parameter function at a single tuple parameter
    Print("{OnPair(Add)}")
    # an override's implementation through the base's variant value
    B:base = derived{}
    G:type{_(:dog):string} = B.Describe
    Print(G(dog{}))
    # the receiver is evaluated once, when the value is made
    H:type{_(:dog):string} = Mk("once").Describe
    Print(H(dog{}))
    Print(H(dog{}))
    # decides methods by variance (int param stays; effects within)
    O := c2{}
    Print("{UseD(O.Pos)}")
