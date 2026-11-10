# A <suspends> dispatch from generic code to an implementation inherited
# by a class that fixes its class's type argument to a compound of its own
# (c3(t) := class(c1(tuple(char, t)))): the dispatch opens c3's t, so the
# implementation's frame is at tuple(char, t'), which the caller has no
# name for, and is kept as an opened override's (#394, #251)
i0(p0:type, p1:type) := interface:
    Mi0(X:p0):string
i1(p0:type) := interface(i0(p0, int)):
    Mi1(X:p0):string
i2(p0:type, p1:type) := interface(i1(p1)):
    Mi2(X:p0):string
    Si2(X:p0)<suspends>:string
    Ti2(X:p0, Y:p1)<suspends>:p1
c1(t0:type) := class(i2(string, t0)):
    Mi2<override>(X:string):string = "c1.Mi2"
    Si2<override>(X:string)<suspends>:string =
        Sleep(0.0)
        "c1.Si2 {X}"
    Ti2<override>(X:string, Y:t0)<suspends>:t0 =
        Sleep(0.0)
        Y
    Mi1<override>(X:t0):string = "c1.Mi1"
    Mi0<override>(X:t0):string = "c1.Mi0"
c3(t0:type) := class(c1(tuple(char, t0))):
    Mi0<override>(X:tuple(char, t0)):string = "c3.Mi0"
GSi2(X:i2(p0, p1), V:p0 where p0:type, p1:type)<suspends>:string = X.Si2(V)
GTi2(X:i2(string, p1), Y:p1 where p1:type)<suspends>:p1 = X.Ti2("t", Y)
Main()<suspends>:void =
    Print(GSi2(c3(int){}, "a"))
    Print(GSi2(c1(int){}, "b"))
    T := spawn{GSi2(c3(char){}, "c")}
    Print(T.Await())
    R := GTi2(c3(int){}, ('x', 7))
    Print("{R(1)}")
