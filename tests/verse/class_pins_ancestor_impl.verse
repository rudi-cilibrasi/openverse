# a class that records pins relating its type arguments to ones past the
# receiver's, using an implementation at or above the receiver's class or
# one that fixes nothing: called without a refinement (#209)
base(a:type) := class:
    A:a
    Name():string = "base"
pair(a:type, b:type) := class(base(a)):
    B:b
    Get():a = A
optpair(t:type) := class(pair(?t, t)):
    Get<override>():?t = option{B}
other := class(base(int)):
    Name<override>():string = "other"
box(t:type) := class:
    V:t
    Get():t = V
e2(t:type) := class(box(t)):
    Get<override>():t = V
p(t:type, w:type) := class(e2(t)):
    W:w
    Name():string = "p"
d(w:type) := class(p(?w, w)):
    Name<override>():string = "d"
Show(X:base(t) where t:type):string = X.Name()
Peek(B:box(t) where t:type):t = B.Get()
Main():void =
    Print(Show(optpair(int){A := false, B := 1}))
    Print(Show(base(int){A := 1}))
    Print(Show(other{A := 1}))
    if (X := Peek(d(int){V := option{4}, W := 2})?) then Print("{X}")
    Print("{Peek(box(int){V := 5})}")
