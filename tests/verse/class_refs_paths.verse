# Classes as references (#34), the corners: set paths through interface
# fields at different places, a write made by the right-hand side through
# the object, sets through a parametric class (a value) to an object,
# recursive hierarchies defined in any order, and classes without instances.

counter := class:
    var Count:int = 0

# `Inner` is at a different place in `b` (after `base`'s field) than in `hasc`
hasc := interface:
    Inner:counter
    Bump():void = set Inner.Count += 1
base := class:
    Z:counter = counter{}
b := class(base, hasc):
    Y:int = 0

pt := struct:
    X:int = 0
    Y:int = 0
obj := class:
    var P:pt = pt{}
    var Arr:[]int = array{0, 0}
    SetY():int =
        set P.Y = 7
        1
    SetA():int =
        if (set Arr[1] = 7) {}
        1

box(t:type) := class:
    Item:t

# `add` comes first and holds `expr`s: its variables start as a `lit`
expr := class<abstract>:
    Eval():int
add := class(expr):
    L:expr
    R:expr
    Eval<override>():int = L.Eval() + R.Eval()
lit := class(expr):
    V:int
    Eval<override>():int = V

# no class implements `ghost`, so code using one is unreachable
ghost := interface:
    var N:int
    Boo():string
Haunt(G:ghost):string =
    set G.N = 3
    "{G.N} {G.Boo()}"

Main():void =
    X := b{Inner := counter{}}
    H:hasc = X
    set H.Inner.Count = 5
    H.Bump()
    Print("Inner {X.Inner.Count} Z {X.Z.Count}")
    O := obj{}
    set O.P.X = O.SetY()
    Print("{O.P.X} {O.P.Y}")
    if (set O.Arr[0] = O.SetA()) {}
    Print("{O.Arr[0] or -1} {O.Arr[1] or -1}")
    Bx := box(counter){Item := counter{}}
    set Bx.Item.Count = 9
    Print("{Bx.Item.Count}")
    E:expr = add{L := lit{V := 1}, R := add{L := lit{V := 2}, R := lit{V := 3}}}
    Print("{E.Eval()}")
    var G:?ghost = false
    if (Gh := G?) then Print(Haunt(Gh)) else Print("no ghost")
