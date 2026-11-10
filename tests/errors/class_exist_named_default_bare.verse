# expect: cannot dispatch Get to class k yet when its default for ?Extra has no type of its own: Get declares ?Extra as u there
# (container declares ?Extra at a bare type parameter, t, which no array{} can be; k's
# default, array{}, would need the type argument the dispatch opens; an internal
# error before)
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
