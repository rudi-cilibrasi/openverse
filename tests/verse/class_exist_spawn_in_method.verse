# a method of a class with a type parameter of its own (below a
# non-generic class) that spawns: it takes its type argument's value as
# usual, as it overrides nothing (#209)
Worker()<suspends>:int =
    Sleep(1.0)
    7
shape := class:
    N:int = 0
box(t:type) := class(shape):
    V:t
    Start():task(int) = spawn{Worker()}
Main()<suspends>:void =
    B := box(string){V := "s"}
    Print("{B.Start().Await()}")
