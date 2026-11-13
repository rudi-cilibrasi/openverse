# `t(X)`: X converted to the type t, of a type that is a subtype of it
# (Book of Verse tests, Cast.versetest 57-87): built-in types, a struct,
# an enum, `(?int)(…)` and `([]int)(…)`, a class and an interface
s := struct{ A:int = 1 }
e := enum{X, Y}
c0 := class{}
c1 := class(c0){}
i0 := interface{}
c2 := class(c1, i0){}
Main()<decides>:void =
    int(0) = 0
    float(0.0) = 0.0
    logic(false) = false
    (?int)(option{0})? = 0
    ([]int)(array{1,2,3}) = array{1,2,3}
    s(s{}).A = 1
    e(e.Y) = e.Y
    void(0)
    void(0.0)
    void("0")
    i0(c2{})
    c0(c1{})
    Print("{int(3) + 4} {string("ab")}")
