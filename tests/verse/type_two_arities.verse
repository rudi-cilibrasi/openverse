# A type alias may take the name of a parametric class, interface or struct
# of another number of type parameters, before or after it: t() := t(int)
# beside t(u:type) := class…; a use names the one of its arity (the Book of
# Verse's tests, ParametricTypes.versetest:754-768, SOL-7503, SOL-7849).
default_param := module:
    class1<public>(t:type) := class:
        Property<public>:int
    class1<public>() := class1(int)
    F1<public>(X:class1()):tuple(class1(), int) = (X, X.Property)
    F4<public>()<transacts>:?class1() = false
    F5<public>():class1() = class1():
        Property := 3
i() := i(void)
i(T:type) := interface:
    Method(X:T):T = X
c := class(i()) {}
c_int := class(i(int)) {}
pair(t:type) := struct:
    First:t
    Second:t
pair() := pair(string)
Main():void =
    if (not default_param.F4()?.Property):
        Print("{default_param.F5().Property} {default_param.F1(default_param.class1(int){Property := 7})(1)}")
    if (c{}.Method(false) = false):
        Print("{c_int{}.Method(10)}")
    P:pair() = pair(){First := "a", Second := "b"}
    Q:pair(int) = pair(int){First := 1, Second := 2}
    Print("{P.First}{P.Second} {Q.First + Q.Second}")
