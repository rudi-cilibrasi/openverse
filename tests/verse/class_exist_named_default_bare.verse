container(t:type) := interface:
    Get(Z:t, ?Extra:t):t
k(a:type) := class(container([]a)):
    X:a
    Get<override>(Z:[]a, ?Extra:[]a = array{}):[]a = Z + Extra + array{X}
G(C:container(u), D:u where u:type):u = C.Get(D)
Main():void =
    T := k(int){X := 1}
    R := G(T, array{5})
    Print("{R.Length}")
