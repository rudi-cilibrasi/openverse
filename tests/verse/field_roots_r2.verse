# regression test for the C runtime's field roots (#50 review, r2): Lean and C must agree
box := class:
    var A:[]int = array{}

F(B:box):void =
    set B.A = array{4, 5, 6}

G(B:box):int =
    set B.A = array{1, 2, 3}
    F(B)
    0

Main():void =
    B := box{}
    G(B)
    Print("{B.A.Length}")
    for (V : B.A) { Print("{V}") }
