# ToString of a float: the Book's API ("Fixed point with exactly six digits
# after the decimal point, always") and Intrinsics/FloatToString.versetest.
# The exact binary value rounded half to even (0.0078125 is 2^-7 exactly, a
# tie), every digit before the point, the sign kept when the digits are all
# zero, NaN, Inf and -Inf; string interpolation calls ToString (ch. 2).
Main():void =
    Print(ToString(0.0))
    Print(ToString(1.0))
    Print(ToString(-1.5))
    Print(ToString(1.2345678901234567))
    Print(ToString(1234567890123456.0))
    Print(ToString(1.0e100))
    Print(ToString(-12.34e100))
    Print(ToString(0.0078125))
    Print(ToString(0.0234375))
    Print(ToString(-0.0078125))
    Print(ToString(0.0000005))
    Print(ToString(0.0000015))
    Print(ToString(-1.0e-300))
    Print(ToString(-0.0))
    Print(ToString(9007199254740993.0))
    Print(ToString(1.0 / 0.0))
    Print(ToString(-1.0 / 0.0))
    Print(ToString(0.0 / 0.0))
    Score:float = 98.5
    Print("Score: {Score}")
    if ("{Score}" = ToString(Score)) then Print("interpolation is ToString")
