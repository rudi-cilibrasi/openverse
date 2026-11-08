# choice (#208) with classes (the join), a generic function, a method,
# function values, a <suspends> function, and an if inside a for
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
cat := class(animal):
    Name<override>():string = "cat"
Pick(X:t, Y:t where t:type)<decides>:t = first{Z := X | Y; Z}
counter := class:
    var N:int = 0
    Bump()<transacts>:int =
        if (K := 1 | 2 | 3, K > N):
            set N = K
        N
Inc(X:int):int = X + 1
Dbl(X:int):int = X * 2
Tick()<suspends>:void =
    if (X := 1 | 2, X > 1) then Print("suspends {X}")
    Sleep(0.0)
Main()<suspends>:void =
    for (A := dog{} | cat{}) { Print(A.Name()) }
    if (P := Pick[1, 2]) then Print("generic {P}")
    C := counter{}
    Print("{C.Bump()} {C.Bump()} {C.Bump()} {C.Bump()}")
    for (F := Inc | Dbl) { Print("{F(5)}") }
    Tick()
    for (X := 1 | 2):
        if (Y := X | 100, Y > 50) then Print("inner {X} {Y}")
