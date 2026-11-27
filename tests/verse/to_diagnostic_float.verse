# ToDiagnostic of a float: the shortest decimal that reads back as it, laid out as Python's repr
# does, which is the format of the Book's tests (Tests/Intrinsics/ToDiagnostic.versetest: "1.5",
# "1e+100", "1.234e+101", "1.7976931348623157e+308", "5e-324", "Inf", "NaN"). The printer is
# Verse code in the ToDiagnostic prelude (diagFloat): it takes the float apart with exact
# halvings and doublings and does the rest in ints. Each line below is Python's repr of the value.
point := struct:
    X:int
    Y:float
D(F:float):void = Print(ToDiagnostic(F).String)
Main():void =
    D(0.0)
    D(1.0)
    D(1.5)
    D(-1.5)
    D(0.1)
    D(0.1 + 0.2)
    D(1.2345678901234567)
    D(1234567890123456.0)
    D(9999999999999998.0)
    D(1.0e16)
    D(1.0e100)
    D(12.34e100)
    D(-12.34e100)
    D(1.7976931348623157e308)
    D(5.0e-324)
    D(2.2250738585072014e-308)
    D(2.225073858507201e-308)
    D(0.0001)
    D(0.00001)
    D(4503599627370496.0)
    D(9007199254740993.0)
    D(1.0e22)
    D(1.0e23)
    D(1.0000000000000002)
    D(0.9999999999999999)
    D(Inf)
    D(-Inf)
    D(NaN)
    Print(ToDiagnostic(point{X := 1, Y := 2.0}).String)
    Print(ToDiagnostic(array{0.5, -2.5e-7}).String)
    Print(ToDiagnostic(option{(2.5, "x")}).String)
    Print(ToDiagnostic(map{1 => 0.25}).String)
