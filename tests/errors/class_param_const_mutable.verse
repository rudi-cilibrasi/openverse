# expect: the constant K would hold an object with var fields
cell(t:type) := class:
    var Value:t
holder(t:type) := class:
    B:t
w(t:type) := class:
    A:?holder(cell(int)) = false
    B:t
K:w(int) = w(int){A := option{holder(cell(int)){B := cell(int){Value := 1}}}, B := 0}
Main():void =
    if (X := K.A?) then set X.B.Value = 5
    if (Y := K.A?) then Print("{Y.B.Value}")
