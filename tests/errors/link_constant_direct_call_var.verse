# expect: computing the constant Count allocates the var N declared in Counted
# A constant whose initialiser calls a function that declares a var: the
# link error of a module constant that allocates a var (OpenVerse, after the
# Book's GlobalVariables.versetest:79, a direct call that allocates a var:
# 9003 on both VMs).
Counted(Limit:int)<computes>:int =
    var N:int = 0
    for (I := 1..Limit):
        set N += 1
    N
Count:int = Counted(3)

Main():void =
    Print("{Count}")
