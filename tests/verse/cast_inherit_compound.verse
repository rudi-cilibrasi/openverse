# A refining cast (#243) to a class that only inherits and gives its parent
# a compound of its own type parameter (c1(t) := class(c0([]t))): its own
# pins relate its type arguments to the object's, as the dispatch to the
# branch refines by; from a prefix interface, and through a view (#351)
i0(p0:type) := interface:
    Mi0(X:p0):string
c0(t0:type) := class(i0(t0)):
    F:t0
    Mi0<override>(X:t0):string = "c0.Mi0"
c1(t0:type) := class(c0([]t0)):
    Dummy():int = 0
j0(p0:type, p1:type) := interface:
    Mj0(X:p0):string
d0(t0:type, t1:type) := class(j0(t0, t0)):
    G:t0
    Mj0<override>(X:t0):string = "d0.Mj0"
d1(t0:type) := class(d0([]t0, int)):
    Dummy():int = 0
Main():void =
    A:[]i0([]tuple(char, int)) = array{c0([]tuple(char, int)){F := array{}}, c1(tuple(char, int)){F := array{('x', 2)}}}
    for (X : A):
        if (C := c1[X]) then Print("c1 {C.F.Length} {C.Mi0(array{})}") else Print("not c1")
    B:[]j0([]int, []int) = array{d0([]int, char){G := array{}}, d1(int){G := array{5, 6}}}
    for (X : B):
        if (D := d1[X]) then Print("d1 {D.G.Length} {D.Mj0(array{1})}") else Print("not d1")
