# Clamp, Min and Max of floats with NaN in each position (#724).
# OpenVerse printed, until Epic's result below (the median of the three, NaN
# ordering above +Inf):
#   clamp val 1.000000 lo 1.000000 hi 0.500000 both NaN
#   clamp swapped 0.500000 1.000000 0.000000 below 0.000000 above 2.000000
#   min NaN NaN max NaN NaN
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-20) printed
#   clamp val NaN lo NaN hi NaN both NaN
#   clamp swapped 0.500000 1.000000 0.000000 below NaN above NaN
#   min NaN NaN max NaN NaN
# Clamp is NaN when any of its arguments is, and the median otherwise.
# OpenVerse now prints it too (#724, Lean and C agreeing).
Main():void =
    N := 0.0 / 0.0
    Print("OVPROBE clamp val {Clamp(N, 0.0, 1.0)} lo {Clamp(0.5, N, 1.0)} hi {Clamp(0.5, 0.0, N)} both {Clamp(0.5, N, N)}")
    Print("OVPROBE clamp swapped {Clamp(0.5, 1.0, 0.0)} {Clamp(5.0, 1.0, 0.0)} {Clamp(-5.0, 1.0, 0.0)} below {Clamp(-1.0, 0.0, N)} above {Clamp(2.0, N, 1.0)}")
    Print("OVPROBE min {Min(N, 1.0)} {Min(1.0, N)} max {Max(N, 1.0)} {Max(1.0, N)}")
