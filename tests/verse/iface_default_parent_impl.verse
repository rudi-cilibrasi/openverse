# no copy where a class of the chain implements the method: the class chain wins
# over an interface's default, as without copies (#53)
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>():[]t = array{V(), V()}
own(t:type) := class(c2(t)):
    X:t
    V<override>():t = X
    Get<override>():[]t = array{X}
sub(t:type) := class(own(t), c2(t)):
    Y:int = 0
G(C:container(u) where u:type):u = C.Get()
H(C:c2(t) where t:type):int = C.Get().Length
Main():void =
    S := sub(int){X := 3}
    Print("{S.Get().Length} {H(S)}")
    O:own(int) = S
    Print("{O.Get().Length}")
