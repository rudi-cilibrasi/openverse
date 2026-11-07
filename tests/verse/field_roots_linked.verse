# a recursion building a linked structure whose nodes hold arrays (#50 review):
# the C runtime skips compactions that cannot reclaim much, so this stays linear
node := class:
    V:int
    var Next:?node = false
    var Tag:[]int = array{}

Build(N:int):node =
    X := node{V := N, Tag := array{N}}
    if (N > 0):
        set X.Next = option{Build(N - 1)}
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
        if (I >= 3) { break }
    Print("{T}")
