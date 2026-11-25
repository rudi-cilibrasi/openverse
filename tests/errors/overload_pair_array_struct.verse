# expect: parameters a call cannot tell apart, (a, a) and ([]a)
# F(:a) beside F(:[]a) are two overloads (#724,
# tests/verse/overload_scalar_array); F(:a, :a) beside F(:[]a) are not: two
# arguments are a tuple, which is an array (the Book's tests,
# Overloading.versetest:265, 3532).
a := struct{}
F(X:a, Y:a):int = 1
F(X:[]a):int = 2
Main():void =
    Print("{F(a{}, a{})}")
