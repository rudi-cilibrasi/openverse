# reading and setting an interface field (#157) on a receiver whose closed
# type arguments rule out a class fixing the interface to another type (#186)
holder(t:type) := interface:
    var Item:t
intbox := class(holder(int)):
    N:int = 0
strbox := class(holder(string)):
    S:string = "s"
base := class:
    X:int = 9
sub(t:type) := class(base, holder(t)):
    Y:int = 1
H(Held:holder(int)):int = Held.Item
Bump(Held:holder(int)):void = set Held.Item = Held.Item + 1
G(Held:holder(t) where t:type):t = Held.Item
Main()<suspends>:void =
    I := intbox{Item := 1}
    Bump(I)
    U := sub(int){Item := 40}
    Bump(U)
    Print("{H(I)} {H(U)} {G(strbox{Item := "a"})} {G(I)}")
