# Clamp, Min and Max of floats with NaN in each position (#724).
Main():void =
    N := 0.0 / 0.0
    Print("OVPROBE clamp val {Clamp(N, 0.0, 1.0)} lo {Clamp(0.5, N, 1.0)} hi {Clamp(0.5, 0.0, N)} both {Clamp(0.5, N, N)}")
    Print("OVPROBE clamp swapped {Clamp(0.5, 1.0, 0.0)} {Clamp(5.0, 1.0, 0.0)} {Clamp(-5.0, 1.0, 0.0)} below {Clamp(-1.0, 0.0, N)} above {Clamp(2.0, N, 1.0)}")
    Print("OVPROBE min {Min(N, 1.0)} {Min(1.0, N)} max {Max(N, 1.0)} {Max(1.0, N)}")
