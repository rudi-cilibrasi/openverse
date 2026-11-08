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
H(H:holder(int)):int = H.Item
Bump(H:holder(int)):void = set H.Item = H.Item + 1
G(H:holder(t) where t:type):t = H.Item
Main()<suspends>:void =
    I := intbox{Item := 1}
    Bump(I)
    U := sub(int){Item := 40}
    Bump(U)
    Print("{H(I)} {H(U)} {G(strbox{Item := "a"})} {G(I)}")
