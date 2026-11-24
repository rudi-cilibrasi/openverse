# (#724) Clamp of floats is NaN when any of its three arguments is, as on
# Epic's Verse VM (UEFN 43.12, 2026-11-20: differential/float-clamp-nan and
# float-minmax-nan); openverse ordered NaN above +Inf and gave a bound or
# the value. Without a NaN it stays the median, so swapped bounds agree.
Main():void =
    N := 0.0 / 0.0
    Print("clamp val {Clamp(N, 0.0, 1.0)} lo {Clamp(0.5, N, 1.0)} hi {Clamp(0.5, 0.0, N)} both {Clamp(0.5, N, N)}")
    Print("clamp swapped {Clamp(0.5, 1.0, 0.0)} {Clamp(5.0, 1.0, 0.0)} {Clamp(-5.0, 1.0, 0.0)} below {Clamp(-1.0, 0.0, N)} above {Clamp(2.0, N, 1.0)}")
    Print("clamp {Clamp(N, 0.0, 1.0)} {Clamp(5.0, 10.0, 1.0)} {Clamp(-3.0, 0.0, 1.0)} {Clamp(0.5, N, 0.0)}")
    Print("all {Clamp(N, N, N)} inf {Clamp(N, -Inf, Inf)} {Clamp(Inf, 0.0, 1.0)} {Clamp(-Inf, 0.0, 1.0)} {Clamp(0.5, -Inf, Inf)}")
    Print("int {Clamp(5, 0, 3)} {Clamp(-5, 3, 0)} {Clamp(2, 0, 3)}")
