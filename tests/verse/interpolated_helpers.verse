# A program whose source uses rationals or ReplaceAll only in a string's
# interpolations gets their helpers, as one that uses them anywhere else
# (#116, #150): rationals compared and rounded, an array's and a string's
# ReplaceAll.
Main():void =
    Print("{if (X := 1 / 3, X < 1 / 2) then "less" else "more"} {if (X := 2 / 4, X = 1 / 2) then "equal" else "not"}")
    Print("{if (X := 7 / 2) then Floor(X) else 0} {if (X := -7 / 2) then Ceil(X) else 0}")
    Print("{"abab".ReplaceAll("a", "c")} {array{1, 2, 1}.ReplaceAll(array{1}, array{7, 8}).Length}")
