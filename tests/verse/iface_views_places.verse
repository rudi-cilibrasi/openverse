# A reference to an interface not seen through views, passed as one above it
# that is (#351): each class's view of it is written at the class's places
# where one holds it (c1(t)'s view of i0 is its first, which it fixes to
# tuple(t, int), not tuple(its second, int)), so that a reference with only
# the first fits it
i0(p0:type) := interface:
    Mi0(X:p0):string
i2(p0:type) := interface(i0(p0)):
    Mi2(X:p0):string
i3(p0:type, p1:type) := interface:
    Mi3(X:p1):string
c0(t0:type, t1:type) := class(i0([]t1), i3(t1, int)):
    Mi0<override>(X:[]t1):string = "c0.Mi0"
    Mi3<override>(X:int):string = "c0.Mi3"
c1(t0:type) := class(i2(tuple(t0, int))):
    Fc1_t0:t0
    Mi2<override>(X:tuple(t0, int)):string = "c1.Mi2"
    Mi0<override>(X:tuple(t0, int)):string = "c1.Mi0"
G5(X:i0(p0), V:p0 where p0:type):string = X.Mi0(V)
Main():void =
    X:i2(tuple(string, int)) = c1(string){Fc1_t0 := "c"}
    Print(G5(X, ("a", 1)))
