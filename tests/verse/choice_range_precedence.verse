# (#208) A range's `..` binds looser than `|` (the Book's precedence 3 for `..`; `|` is above the
# comparisons): `7 | 1..2` is `(7 | 1)..2`, and `1..2 | 7` is `1..(2 | 7)`.
Show(A:[]int):string = Join(for (X : A) { "{X}" }, ",")
Main():void =
    Print("7 | 1..2: [{Show(for (X := 7 | 1..2) { X })}]")
    Print("1..2 | 4: [{Show(for (X := 1..2 | 4) { X })}]")
