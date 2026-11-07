# floats (#127): literals, arithmetic, int * float, NaN and infinities, conversions, Min/Max/Abs, set op=, ToString
Area(R:float):float = 3.14159 * R * R
Main():void =
    X:float = 98.5
    Print("Score: {X}")
    Print("{1.0} {0.1 + 0.2} {1.0e16} {1.5e-7} {2.0 / 3.0} {-0.0} {1.0 / 0.0} {-1.0 / 0.0} {0.0 / 0.0}")
    Count:int = 5
    Print("{Count * 1.5} {2.0 * Count} {Area(2.0)}")
    if (0.0 / 0.0 = 0.0 / 0.0) then Print("NaN equals itself")
    if (not (0.0 / 0.0 < 1.0)) then Print("NaN is not less")
    if (1.5 < 2.5, 2.5 <= 2.5, 3.0 > 2.0, 2.0 >= 2.0, 1.0 <> 2.0) then Print("ordered")
    if (A := Round[2.5], B := Round[3.5], C := Floor[-1.5], D := Ceil[-1.5], E := Int[-1.7]) then Print("{A} {B} {C} {D} {E}")
    if (not Floor[1.0 / 0.0]) then Print("Floor of Inf fails")
    if (not Int[0.0 / 0.0]) then Print("Int of NaN fails")
    Print("{Abs(-2.5)} {Min(1.0, 2.0)} {Max(1.0, 2.0)} {Min(0.0 / 0.0, 5.0)} {Max(5.0, 0.0 / 0.0)}")
    var V:float = 1.0
    set V += 0.5
    set V *= 4.0
    set V -= 1.0
    set V /= 2.0
    set V *= 2
    Print("{V} {-V}")
    Fs:[]float = array{1.0, 2.5, 4.0}
    var S:float = 0.0
    for (F : Fs) { set S += F }
    Print("{S} {ToString(1.0e300 * 1.0e10)}")
