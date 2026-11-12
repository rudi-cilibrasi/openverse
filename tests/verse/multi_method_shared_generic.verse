# Generic classes' methods with several values whose name another class has
# too (#283): the family's function is generic over the class's type
# parameters, inferred from the receiver; an override in a class that fixes
# them (ibox) dispatches in its own family; the other family's is ordinary.
box(t : type) := class:
    Item : t
    Vals()<transacts>:t = Item | Item
ibox := class(box(int)):
    Vals<override>()<transacts>:int = Item + 1 | (super:)Vals()
pair(t : type) := class:
    L : t
    R : t
    Vals()<transacts>:t = L | R
counter := class:
    Vals()<transacts>:int = 42
Swap(P : pair(string))<transacts>:string = P.Vals() + "!"
Main()<transacts>:void =
    for (X := box(int){Item := 7}.Vals()):
        Print("box {X}")
    B : box(int) = ibox{Item := 3}
    for (X := B.Vals()):
        Print("ibox {X}")
    for (X := pair(string){L := "l", R := "r"}.Vals()):
        Print("pair {X}")
    for (X := Swap(pair(string){L := "x", R := "y"})):
        Print("swap {X}")
    for (X := pair(int){L := 1, R := 2}.Vals(), Y := box(int){Item := X * 10}.Vals()):
        Print("both {X} {Y}")
    Print("counter {counter{}.Vals()}")
