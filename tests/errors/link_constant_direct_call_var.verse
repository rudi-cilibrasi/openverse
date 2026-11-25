# expect: computing the constant Count allocates the var N declared in Counted
# A constant whose initialiser calls a function that declares a var: the
# link error of a module constant that allocates a var (OpenVerse, after the
# Book's GlobalVariables.versetest:79, a direct call that allocates a var:
# 9003 on both VMs).
# Run with --extended-defaults: without it the call itself is refused first,
# as Epic's compiler does (3582, a data member calls only converging
# functions, UEFN 43.12), and the link check is not reached.
Counted(Limit:int)<computes>:int =
    var N:int = 0
    for (I := 1..Limit):
        set N += 1
    N
Count:int = Counted(3)

Main():void =
    Print("{Count}")
