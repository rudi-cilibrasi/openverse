# expect: F is instantiated at ever larger types
# Polymorphic recursion through a parametric struct is bounded by its Verse Core size.
d(t:type) := struct:
    A:t
    B:t

F(X:t, N:int where t:type):int =
    if (N > 0) then F(d(t){A := X, B := X}, N - 1) else 0

Main():void =
    Print("{F(1, 3)}")
