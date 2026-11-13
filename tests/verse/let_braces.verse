# let takes its definitions in parentheses, before its body, or in braces,
# before `do` and its body (Tim Sweeney's tests: `let{x:=3}do{x+1}`); the
# definitions are visible in the body only.
Main():void =
    N := let{X := 3} do X + 1
    M := let{Y := 4; Z := 5} do {Y * Z}
    P := let(W := 6){W - 1}
    Print("{N} {M} {P}")
