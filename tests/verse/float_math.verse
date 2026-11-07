# the mathematical functions of floats, IsFinite, PiFloat/Inf/NaN, and NaN <= NaN (#132)
Main():void =
    Print("{Sqrt(2.0)} {Sqrt(-1.0)} {Sqrt(Inf)} {Pow(2.0, 10.0)} {Pow(0.0, 0.0)} {Pow(NaN, 0.0)} {Pow(1.0, NaN)}")
    Print("{Exp(1.0)} {Exp(-Inf)} {Ln(0.0)} {Ln(-1.0)} {Ln(Exp(2.0))} {Log(10.0, 100.0)} {Log(2.0, 1024.0)}")
    Print("{Sin(0.0)} {Cos(0.0)} {Sin(PiFloat / 2.0)} {Sin(Inf)} {Sin(NaN)} {Tan(PiFloat / 4.0)}")
    Print("{ArcSin(2.0)} {ArcCos(-5.0)} {ArcSin(NaN)} {ArcTan(1.0) * 4.0} {ArcTan(1.0, -1.0)} {PiFloat}")
    if (F := IsFinite[1.5]) then Print("finite {F}")
    if (not IsFinite[Inf], not IsFinite[-Inf], not IsFinite[NaN]) then Print("not finite")
    if (NaN <= NaN, NaN >= NaN, not NaN < NaN, not NaN > NaN, not NaN <= 1.0, not 1.0 >= NaN) then Print("NaN orders with itself only by <= and >=")
