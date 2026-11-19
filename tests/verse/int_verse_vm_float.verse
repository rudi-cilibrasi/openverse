# An int beyond 64 bits times a float (#724): the int is converted to the
# nearest double, ties to even (as every int is, IEEE's default rounding),
# and to an infinity past the largest double (Python's float(int) agrees
# but raises OverflowError there). Floor, Ceil, Round and Int of a float
# stay 64-bit: a result outside 64 bits is the overflow error
# (float_to_int_range), as the Book's API reference says of each.
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    P := Big * 2
    if (Big * 1.0 = 9223372036854775808.0) then Print("2^63")
    if ((P + 2048) * 1.0 = 18446744073709551616.0) then Print("2^64 + 2^11: a tie, to even")
    if ((P + 2049) * 1.0 = 18446744073709555712.0) then Print("2^64 + 2^11 + 1: up")
    if ((P + 6144) * 1.0 = 18446744073709559808.0) then Print("2^64 + 3 * 2^11: a tie, to even, up")
    if (-(P + 2049) * 1.0 = -18446744073709555712.0) then Print("negative")
    var X:int = Big
    for (I := 1..4):
        set X *= X
    # 2^1008: exact
    if (X * 1.0 = 2.7430620343968443e+303) then Print("2^1008")
    set X *= Big
    if (X * 1.0 = Inf, -X * 1.0 = -Inf) then Print("2^1071: infinity")
    if (F := Floor[Big * 1.0]) then Print("unreachable {F}")
    Print("not reached")
