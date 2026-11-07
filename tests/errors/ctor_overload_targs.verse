# expect: the overloads of constructor K construct box at different type arguments
box(t:type) := class:
    X:?t = false
    Y:int = 3
K<constructor>(A:int) := box(int):
    X := option{A}
K<constructor>(S:string) := box(string):
    Y := 5
Main():void =
    C := K("s")
    if (Q := C.X?) then Print("{Q + 1}")
    D:box(int) = K("t")
    Print("{C.Y} {D.Y}")
