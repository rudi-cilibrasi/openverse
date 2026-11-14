# expect: F sets a var field, which its effects (<reads>) do not allow
# <computes><reads> allows reading and nothing else of the heap (Book of
# Verse ch. 13: <computes> is exclusive, <reads> additive)
c := class{var N:int = 0}
F(C:c)<computes><reads>:int =
    set C.N = 1
    C.N
Main():void = Print("{F(c{})}")
