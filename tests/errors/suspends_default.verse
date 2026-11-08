# expect: G suspends: it can only be called in a <suspends> function
G(N:int)<suspends>:int = N
F(A:int, ?K:int = G(1)):int = A + K
Main()<suspends>:void = Print("{F(1)}")
