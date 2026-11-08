# choice (#208) as the value of set: the indices of the path, then (for op=)
# the old value, then the choice, as set evaluates; the alternatives at the
# destination's type; nested joins past the retry bound
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
cat := class(animal):
    Name<override>():string = "cat"
Id(X:t where t:type):t = X
Idx(I:int):int =
    Print("idx {I}")
    I
Main():void =
    var N:int = 0
    if (set N += (set N = 10; 1) | 2):
        Print("{N}")
    var A:[]int = array{9}
    if (set A = array{} | array{1}):
        Print("{A.Length}")
    var O:?int = false
    if (set O = false | option{1}):
        Print("{if (V := O?) then V else -1}")
    var B:[]int = array{0, 0, 0}
    var K:int = 0
    if (set B[Idx(K)] = (set K = 2; 5) | 6, B[0] = 6):
        for (E : B) { Print("B {E}") }
        Print("K {K}")
    var C:[]int = array{1, 2}
    if (set C[1] += (Print("rhs"); 10) | 20, C[1] > 15) then for (E : C) { Print("C {E}") }
    if (A2 := 1 | first{X2 := 1 | first{X1 := 1 | first{X0 := 1 | Id(1 / 2); X0}; X1}; X2}) then Print("{Floor(A2)}")
    if (Z := first{Q := 1 | first{R := 1 | first{S := 1 | first{T := dog{} | cat{}; T}; S}; R}; Q}) then Print("joined")
