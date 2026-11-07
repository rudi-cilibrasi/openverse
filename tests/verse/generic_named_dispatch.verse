# a generic method's named argument through dispatch infers its own type parameter (#119 review)
box := class:
    Pair(X:u, ?Z:u = X where u:type):tuple(u, u) = (X, Z)
sub := class(box):
    Pair<override>(X:u, ?Z:u = X where u:type):tuple(u, u) = (Z, X)
Main():void =
    B:box = sub{}
    Q := B.Pair("a", ?Z := "z")
    Print("{Q(0)} {Q(1)}")
