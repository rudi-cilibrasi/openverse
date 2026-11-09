# <suspends> overrides in classes with type parameters that their parent's
# type arguments do not give (#251): a dispatch from expr(t) opens them, so
# the caller has no names for the callee's frame's type arguments. It holds
# the frame without them, resumes and cancels it through dispatches that
# open them, and reads the result from a cell of its own type, which the
# frame writes when it is done.
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
num := class(expr(int)):
    V:int
    Eval<override>()<suspends>:int =
        Sleep(0.1)
        V
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>()<suspends>:tuple(a, b) = (L.Eval(), R.Eval())
fstE(a:type, b:type) := class(expr(a)):
    P:expr(tuple(a, b))
    Eval<override>()<suspends>:a = P.Eval()(0)
sndE(a:type, b:type) := class(expr(b)):
    P:expr(tuple(a, b))
    Eval<override>()<suspends>:b = P.Eval()(1)
Run(E:expr(t) where t:type)<suspends>:t = E.Eval()
Main()<suspends>:void =
    P := pairE(int, int){L := num{V := 1}, R := num{V := 2}}
    Print("{Run(fstE(int, int){P := P})} {Run(sndE(int, int){P := P})}")
    Q := pairE(tuple(int, int), int){L := P, R := num{V := 3}}
    R := Run(Q)
    Print("{R(0)(0)} {R(0)(1)} {R(1)}")
    Print("{Run(fstE(tuple(int, int), int){P := Q})(1)}")
