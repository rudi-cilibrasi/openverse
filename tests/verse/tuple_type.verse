# tuple(), also written true, is the type of the empty value alone; void
# takes any value (Book of Verse ch. 2, "void, true, tuple() and false"):
# false, () and a void value convert to tuple(), which converts to void, to
# an array (a tuple is the array of its elements) and, "true is a subtype of
# logic", to logic as false. So tuple() and int are distinct overloads, and
# the extension methods of the Book's ExtensionFields test are.
F(:tuple()):int = 1
F(X:int):int = 2 + X
G(X:tuple()):tuple() = X
EmptyTupleFunc(Arg1:tuple()):void = {}
TrueOutput(:int):true = {}
TrueInput(:true):int = 42
(X:tuple()).Extension():int = 42
(A:int).Extension():int = 10 * A
(AB:tuple(int, int)).Extension():int = 10 * AB(0) + 100 * AB(1)
Main():void =
    Print("{F()} {F(())} {F(false)} {F(5)}")
    if (G() = (), G(false) = false) then Print("unit")
    EmptyTupleFunc()
    X:tuple() = if (false?) then () else false
    Y:tuple() = false
    if (X = (), Y = false, X = Y) then Print("x y")
    Flag:true = false
    AsLogic:logic = Flag
    if (not AsLogic?, AsLogic = false) then Print("flag")
    if (TrueOutput(0) = false) then Print("true out")
    Print("{TrueInput(false)} {TrueInput(())}")
    Print("{().Extension()} {1.Extension()} {(1, 2).Extension()}")
    A:[]int = Y
    Print("{A.Length}")
