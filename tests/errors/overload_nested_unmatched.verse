# expect: 8:47: no overload of Depth takes (int)
# A nested call of an overloaded function whose innermost argument no overload
# takes (#769): the refusal is the innermost call's, and comes at once. Each
# level asked for its argument five times over, so these six levels took four tenths of a second, ten two minutes.
Depth(S:string):int = 0
Depth(C:char):int = 2
Main():void =
    Print("{Depth(Depth(Depth(Depth(Depth(Depth(1))))))}")
