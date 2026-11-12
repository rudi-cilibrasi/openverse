# An interface's default method, declared in an interface referred to through
# views (i0, which c4 gives []t0), called through one below it that is not
# (i1): the receiver is converted to i0, narrowed to the classes whose view
# can be it, before the direct call of the default (#351)
i0(p0:type) := interface:
    var Qi0_0:string
    D_Qi0_0():string = Qi0_0
    Qi0_1:p0
    Mi0(X:p0):string
i1(p0:type) := interface(i0(?p0)):
    var Qi1_0:char
    var Qi1_1:p0
    Mi1(X:p0):string
i2(p0:type) := interface:
    Mi2(X:p0):string
c1(t0:type, t1:type) := class(i1(t0), i2(?t1)):
    Mi1<override>(X:t0):string = "c1.Mi1"
    Mi0<override>(X:?t0):string = "c1.Mi0"
    Mi2<override>(X:?t1):string = "c1.Mi2"
    var Qi0_0<override>:string = "c"
c2(t0:type, t1:type) := class(i1(char), i2(?t0)):
    Mi1<override>(X:char):string = "c2.Mi1"
    Mi0<override>(X:?char):string = "c2.Mi0"
    Mi2<override>(X:?t0):string = "c2.Mi2"
c4(t0:type, t1:type) := class(i2(t1), i0([]t0)):
    Mi2<override>(X:t1):string = "c4.Mi2"
    Mi0<override>(X:[]t0):string = "c4.Mi0"
Sh_string(X:string):string = X
Main():void =
    A2:[]i1(string) = array{c1(string, string){Qi1_0 := 'y', Qi1_1 := "a", Qi0_1 := option{"b"}}}
    for (X : A2):
        Print(Sh_string(X.D_Qi0_0()))