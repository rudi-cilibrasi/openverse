# (#53) a cast to an interface that gives its parent type arguments of its
# own opens them: a test of each class below both, each of whose branches
# calls the one function the branch is made into, at that class's
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    Size():int
    Name():string
box(t:type) := class(c2(t)):
    V:t
    Get<override>():[]t = array{V, V}
    Size<override>():int = 2
    Name<override>():string = "box"
sbox(t:type) := class(box(t)):
    Name<override>():string = "sbox"
tb(a:type, b:type) := class(c2(tuple(a, b))):
    A:a
    B:b
    Get<override>():[]tuple(a, b) = array{(A, B)}
    Size<override>():int = 1
    Name<override>():string = "tb"
ib := class(c2(int)):
    Get<override>():[]int = array{1, 2, 3}
    Size<override>():int = 3
    Name<override>():string = "ib"
plain(t:type) := class(container(t)):
    W:t
    Get<override>():t = W
Count(Xs:[]t where t:type):int = Xs.Length
Firsts(Xs:[]t where t:type)<decides>:t = Xs[0]
# u = []t', t' opened: the branch is generic over t', whose value each
# class's test gives (box's and tb's from their hidden fields, ib's int)
Try(C:container(u) where u:type):string =
    if (B := c2[C]) then "{B.Name()} {B.Size()} {Count(B.Get())}" else "not c2"
# its value at the code's own type: u = []t', so the branch's []t' is a u
Again(C:container(u) where u:type):?u =
    if (B := c2[C]) then option{B.Get()} else false
# in a for's clauses, and the object a call, evaluated once
counter := class:
    var N:int = 0
Pick(K:counter, Cs:[]container(u), I:int where u:type)<transacts><decides>:container(u) =
    set K.N += 1
    Cs[I]
Sizes(Cs:[]container(u) where u:type):[]int =
    for (C : Cs, B := c2[C]) { B.Size() }
Main()<transacts>:void =
    Print(Try(box(string){V := "x"}))
    Print(Try(sbox(int){V := 1}))
    Print(Try(tb(int, string){A := 1, B := "b"}))
    Print(Try(ib{}))
    Print(Try(plain(int){W := 4}))
    if (V := Again(box(int){V := 7})?) then Print("again {V.Length}")
    if (V := Again(plain([]int){W := array{5}})?) then Print("no") else Print("none")
    Cs:[]container([]int) = array{box(int){V := 3}, plain([]int){W := array{}}, ib{}}
    for (S : Sizes(Cs)) { Print("size {S}") }
    K := counter{}
    if (B := c2[Pick[K, Cs, 2]]) then Print("picked {B.Name()} {K.N}")
    # (the call's write is undone when the object is no c2, or has none)
    if (B := c2[Pick[K, Cs, 1]]) then Print("no") else Print("not c2 {K.N}")
    if (B := c2[Pick[K, Cs, 5]]) then Print("no") else Print("none {K.N}")
