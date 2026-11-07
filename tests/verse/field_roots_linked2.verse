# a recursion building a linked structure that also replaces a field's own
# array at each level (#50 review): Lean and C agree, and the C runtime stays linear
node := class:
    V:int
    var Next:?node = false
    var Tag:[]int = array{}

# post-order: a node's own array field is updated after the recursive call
Build(N:int):node =
    X := node{V := N, Tag := array{N}}
    if (N > 0):
        set X.Next = option{Build(N - 1)}
        set X.Tag = X.Tag + array{0}
    X

Main():void =
    var T:int = 0
    var I:int = 0
    loop:
        set I += 1
        L := Build(2000)
        var Cur:?node = option{L}
        loop:
            if (C := Cur?):
                set T += C.Tag.Length
                set Cur = C.Next
            else:
                break
        if (I >= 20) { break }
    Print("{T}")
