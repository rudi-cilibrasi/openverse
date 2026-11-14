# (super:)M in an override of M, as the Book has it: in a block of its body,
# in a spawn in it, and of another overload of M above (Super.versetest,
# SOL-9691-CaptureSuper.versetest)
base := class:
    Foo()<transacts>:int = 42
    Pick(N:int):string = "int {N}"
    Pick(S:string):string = "str {S}"
    Init()<suspends>:void =
        Sleep(0.1)
        Print("base init")
mid := class(base):
    Foo<override>()<transacts>:int = block{(super:)Foo()} + 25
    Pick<override>(N:int):string = "mid {(super:)Pick("{N}")}"
    Init<override>()<suspends>:void =
        T := spawn{(super:)Init()}
        T.Await()
        Print("mid init")
Main()<suspends>:void =
    M := mid{}
    Print("{M.Foo()}")
    Print(M.Pick(3))
    M.Init()
