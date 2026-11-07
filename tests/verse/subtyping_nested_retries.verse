# regression test from the #67 review (b_20): nested retries stay fast
shape := class<abstract>:
    Area():int
square := class(shape):
    S:int
    Area<override>():int = S * S
circle := class(shape):
    R:int
    Area<override>():int = 3 * R * R
Main():void =
    C := 3
    X := (if (C > 20) then array{square{S := 1}} else {Z20 := (if (C > 19) then array{square{S := 1}} else {Z19 := (if (C > 18) then array{square{S := 1}} else {Z18 := (if (C > 17) then array{square{S := 1}} else {Z17 := (if (C > 16) then array{square{S := 1}} else {Z16 := (if (C > 15) then array{square{S := 1}} else {Z15 := (if (C > 14) then array{square{S := 1}} else {Z14 := (if (C > 13) then array{square{S := 1}} else {Z13 := (if (C > 12) then array{square{S := 1}} else {Z12 := (if (C > 11) then array{square{S := 1}} else {Z11 := (if (C > 10) then array{square{S := 1}} else {Z10 := (if (C > 9) then array{square{S := 1}} else {Z9 := (if (C > 8) then array{square{S := 1}} else {Z8 := (if (C > 7) then array{square{S := 1}} else {Z7 := (if (C > 6) then array{square{S := 1}} else {Z6 := (if (C > 5) then array{square{S := 1}} else {Z5 := (if (C > 4) then array{square{S := 1}} else {Z4 := (if (C > 3) then array{square{S := 1}} else {Z3 := (if (C > 2) then array{square{S := 1}} else {Z2 := (if (C > 1) then array{square{S := 1}} else {Z1 := array{circle{R := 1}}; array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}}); array{circle{R := 1}}})
    Print("{X.Length}")
