# regression test for the C runtime's field roots (#50 review, r4): Lean and C must agree
box := class:
    var A:[]int = array{}

F(B:box):int =
    set B.A = array{4}
    set B.A = array{}
    0

G(B:box):int =
    set B.A = array{1, 2, 3}
    if (F(B) > 5) {}
    0

H(B:box):int =
    G(B)
    0

Main():void =
    B := box{}
    H(B)
    X := array{7, 8, 9, 10, 11}
    Print("{X.Length} {B.A.Length}")
    for (V : B.A) { Print("{V}") }
