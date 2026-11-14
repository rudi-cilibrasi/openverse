# Interfaces referred to through views (#351): a class below one has its own
# pins as Verse Core pins (c3's second type argument is its first), which
# a variable's initial object needs where the view gives only the first;
# and a reference whose classes include one whose view gives other, closed,
# type arguments (c2 gives i0 ?char) is narrowed to the others when it is
# passed as one seen through views
i0(p0:type, p1:type) := interface:
    var Qi0_0:p1
    var Qi0_1:p1
i4(p0:type) := interface:
    var Qi4_0:string
c0(t0:type, t1:type) := class<abstract>(i0(t0, t1)):
    Fc0_t0:t0
c3(t0:type) := class(c0(t0, t0), i4([]t0)):
    var Qi4_0<override>:string = "a"
j0(p0:type) := interface:
    var Qj0_0:string
    Mj0(X:p0):string
j1(p0:type) := interface(j0(?p0)):
    Mj1(X:p0):string
j2(p0:type) := interface:
    Mj2(X:p0):string
d1(t0:type, t1:type) := class(j1(t0), j2(?t1)):
    Mj1<override>(X:t0):string = "d1.Mj1"
    Mj0<override>(X:?t0):string = "d1.Mj0"
    Mj2<override>(X:?t1):string = "d1.Mj2"
    var Qj0_0<override>:string = "c"
d2(t0:type, t1:type) := class(j1(char), j2(?t0)):
    Mj1<override>(X:char):string = "d2.Mj1"
    Mj0<override>(X:?char):string = "d2.Mj0"
    Mj2<override>(X:?t0):string = "d2.Mj2"
d4(t0:type, t1:type) := class(j2(t1), j0([]t0)):
    Mj2<override>(X:t1):string = "d4.Mj2"
    Mj0<override>(X:[]t0):string = "d4.Mj0"
# (j0 only takes its type argument in, so a j0(p0) would give no p0, the
# Book's rule, ParametricFunctions.versetest 356: the type is written)
GQ(X:j0(?string)):string = X.Qj0_0
Main():void =
    A:[]i4([]char) = array{c3(char){Fc0_t0 := 'z', Qi0_0 := 'y', Qi0_1 := 'x', Qi4_0 := "b"}}
    for (X : A) { Print(X.Qi4_0) }
    B:[]j1(string) = array{d1(string, string){Qj0_0 := "q"}}
    for (X : B) { Print("{GQ(X)} {X.Mj0(option{"s"})}") }
