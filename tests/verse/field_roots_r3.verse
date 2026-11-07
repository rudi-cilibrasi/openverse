# regression test for the C runtime's field roots (#50 review, r3): Lean and C must agree
stack := class:
    var Items:[]int = array{}
    Push(X:int):void =
        set Items = Items + array{X}

Fill(S:stack):void =
    S.Push(1)
    S.Push(2)
    S.Push(3)

Main():void =
    S := stack{}
    Fill(S)
    Print("{S.Items.Length}")
