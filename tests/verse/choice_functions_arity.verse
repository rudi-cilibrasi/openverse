# functions with several values (#235), review case my-arity
Sum(Xs:[]int):int = Xs.Length | Xs.Length * 10
Pair(A:int, B:int):int = A + B | A * B
Main():void =
    for (V := Sum(1, 2, 3)) { Print("sum {V}") }
    T := (3, 4)
    for (V := Pair(T)) { Print("pair {V}") }
