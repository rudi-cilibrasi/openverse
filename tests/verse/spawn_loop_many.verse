# a loop that spawns many tasks, in a suspends function, and a for whose
# element a later suspension needs (#225): the element is kept in the
# frame, and binding it in the loop's condition must not copy the heap
Tick(N:int)<suspends>:void =
    Sleep(1.0)
Sum(Xs:[]int)<suspends>:int =
    var S:int = 0
    for (X : Xs):
        Sleep(0.0)
        if (Y := option{X}?):
            Sleep(0.0)
            set S += Y
    S
Main()<suspends>:void =
    for (I := 1..5000):
        spawn{Tick(I)}
    Sleep(2.0)
    Print("{Sum(array{1, 2, 3, 4})}")
