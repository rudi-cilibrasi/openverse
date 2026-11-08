# function values (#210): function types (both syntaxes), functions passed,
# stored and called, fields, options, modules, recursion through a value,
# a tuple flattened into parameters
M := module:
    Triple<public>(X:int):int = 3 * X
using{M}
Double(X:int):int = 2 * X
Inc(X:int):int = X + 1
Add(X:int, Y:int):int = X + Y
Twice(F:type{_(:int):int}, X:int):int = F(F(X))
Apply(F:int->int, X:int):int = F(X)
Sum(Xs:[]int, F:[]int->int):int = F(Xs)
Total(Xs:[]int):int =
    var S:int = 0
    for (X : Xs) { set S += X }
    S
Fact(N:int):int = if (N <= 1) then 1 else N * Apply(Fact, N - 1)
Pick(B:logic):int->int = if (B?) then Double else Inc
Seven():int = 7
Hello():void = Print("hello")
Run(F:type{_():int}):int = F()
Do(F:type{_():void}):void =
    F()
    F()
holder := class:
    Op:int->int
    Run(X:int):int = Op(X)
Main():void =
    Print("{Twice(Double, 3)} {Twice(Inc, 3)} {Apply(Double, 5)}")
    G := Inc
    Print("{G(10)}")
    Fs:[]type{_(:int):int} = array{Double, Inc, M.Triple}
    for (F : Fs) { Print("{F(7)}") }
    Print("{Apply(M.Triple, 2)} {Apply(Triple, 3)} {Sum(array{1, 2, 3}, Total)} {Fact(5)}")
    var V:int->int = Fact
    set V = Pick(false)
    Print("{V(4)} {Pick(true)(4)}")
    O:?(int->int) = option{V}
    if (H := O?) then Print("{H(1)}")
    H := holder{Op := Double}
    Print("{H.Run(4)} {H.Op(5)}")
    P:tuple(int, int)->int = Add
    T := (3, 4)
    Print("{P(1, 2)} {P(T)}")
    Print("{Run(Seven)}")
    Do(Hello)
