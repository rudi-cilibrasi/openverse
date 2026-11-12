# A <suspends> interface default reached through an upcast to an interface
# seen through views from one that is not (#351), as iface_views_places
i0(p0:type, p1:type) := interface:
    D0():char = 'z'
    Mi0(X:p1):string
i1(p0:type) := interface(i0(string, p0)):
    Mi1(X:p0):string
i2(p0:type, p1:type) := interface:
    M2():int
i3(p0:type) := interface:
    Mi3(X:p0):string
i4(p0:type, p1:type) := interface:
    Mi4(X:p1):string
c0(t0:type, t1:type, t2:type) := class<abstract>(i3(t0), i1(?t2), i2(t1, t1)):
    Fc0_t0:t0
    Fc0_t2:t2
    Mi3<override>(X:t0):string = "c0.Mi3"
c1(t0:type, t1:type) := class<abstract>(i2(t1, ?t1), i0(t0, []t0)):
    Fc1_t1:t1
c3 := class(c0(?char, ?string, char), i4(int, int)):
    Mi1<override>(X:?char):string = "c3.Mi1"
    Mi0<override>(X:?char):string = "c3.Mi0"
    Mi4<override>(X:int):string = "c3.Mi4"
    M2<override>():int = 2
GSF_Qi0_0(X:i0(p0, p1) where p0:type, p1:type)<suspends>:char =
        X.D0()
Sh_char(X:char):string = "{X}"
Main()<suspends>:void =
    X:i1(?char) = c3{Fc0_t0 := option{'y'}, Fc0_t2 := 'z'}
    Print(Sh_char(GSF_Qi0_0(X)))
