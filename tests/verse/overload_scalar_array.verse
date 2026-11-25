# F(:t) beside F(:[]t) (#724): one argument is no tuple of the arguments, so
# it is an array only when its own type is one, and the two are distinct
# overloads (the Book's tests, Overloading.versetest:260, valid; Epic's
# compiler and Verse VM, UEFN 43.12,
# followup-refused/overloads-struct-and-array: one 1 many 2). A call takes
# the overload its argument's type fits: a tuple of several elements is an
# array, as an empty array{} is.
a := struct{}
F(X:a):int = 1
F(X:[]a):int = 2
G(X:int):string = "one"
G(X:[]int):string = "many"
c := class:
    M(X:float):int = 1
    M(X:[]float):int = 2

Main():void =
    Print("one {F(a{})} many {F(array{a{}})} {F(array{})} {F((a{}, a{}))}")
    Print("{G(1)} {G(array{1, 2})} {G(array{})} {G((1, 2))}")
    Print("{c{}.M(1.0)} {c{}.M(array{1.0})}")
    X:int = 5
    Xs:[]int = array{X}
    Print("{G(X)} {G(Xs)}")
