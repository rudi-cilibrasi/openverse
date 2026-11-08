# the Book's array methods and Concatenate (#150)
Show(A:[]int):string =
    var S:string = ""
    for (X : A) { set S += "{X} " }
    S
Main():void =
    A := array{10, 20, 30, 20, 40}
    if (B := A.RemoveFirstElement[20], C := A.ReplaceFirstElement[20, 99], D := A.Remove[1, 3]) then
        Print("{Show(B)}| {Show(C)}| {Show(D)}")
    if (not A.RemoveFirstElement[7], not A.Remove[3, 2], not A.Remove[-1, 0], not A.Remove[0, 9]) then Print("fails")
    if (E := A.Remove[2, 2]) then Print(Show(E))
    Print("{Show(A.RemoveAllElements(20))}| {Show(A.ReplaceAllElements(20, 0))}| {Show(A.RemoveAllElements(5))}")
    Print(Show(array{1, 2, 3, 4, 2, 3, 5}.ReplaceAll(array{2, 3}, array{99})))
    Print(Show(array{1, 2, 2, 1, 2, 2, 1}.ReplaceAll(array{2, 2}, array{9, 9, 9})))
    Print("Hello World".ReplaceAll("o", "0"))
    Print(Show(array{1, 2}.ReplaceAll(array{}, array{5})))
    Print(Show(Concatenate(array{1, 2}, array{3, 4})))
    Print(Show(Concatenate(array{1, 2}, array{}, array{3})))
    Print(Show(Concatenate(array{array{1, 2, 3}})))
    E2:[]int = Concatenate()
    Print("{E2.Length}")
