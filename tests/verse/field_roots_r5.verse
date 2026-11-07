# regression test for the C runtime's field roots (#50 review, r5): Lean and C must agree
node := class:
    var Items:[]int = array{}

Build(N:node, K:int):void =
    if (K > 0):
        set N.Items = N.Items + array{K}
        Build(N, K - 1)

Main():void =
    N := node{}
    Build(N, 4)
    Print("{N.Items.Length}")
