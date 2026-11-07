# expect: box is parametric: write box(…) with 1 type argument(s)
box(t:type) := struct:
    Value:t

Main():void =
    B := box{Value := 1}
