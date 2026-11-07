# Heap effect specifiers (#35; the spec draft's TransactFx): <computes>,
# <reads>, <writes>, <allocates>, <transacts>. A function with none has
# them all.

counter := class:
    var Count:int = 0
    Get()<reads>:int = Count
    Bump()<transacts>:void = set Count += 1

point := class:
    X:int
    # immutable fields have no heap effect
    Sum(O:point)<computes>:int = X + O.X

token := class<unique>:
    N:int

# a var local is not a heap effect
Total(Cs:[]counter)<reads>:int =
    var T:int = 0
    for (C : Cs) { set T += C.Get() }
    T

Reset(C:counter)<writes>:void = set C.Count = 0
Make()<allocates>:counter = counter{}
NewToken(N:int)<allocates>:token = token{N := N}
Twice(X:int)<computes>:int = X + X
Swap(A:counter, B:counter)<reads><writes>:void =
    T := A.Count
    set A.Count = B.Count
    set B.Count = T

# a constant has the effects of its initialiser
Origin:point = point{X := 0}
Half<computes>:int = Twice(Origin.X + 5)

Main():void =
    C := Make()
    C.Bump()
    C.Bump()
    D := Make()
    D.Bump()
    Print("{Total(array{C, D})}")
    Swap(C, D)
    Print("{C.Get()} {D.Get()}")
    Reset(C)
    Print("{C.Get()} {Twice(21)} {point{X := 1}.Sum(point{X := 2})} {Half}")
    if (NewToken(1) <> NewToken(1)) then Print("tokens differ")
