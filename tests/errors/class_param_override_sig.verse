# expect: swap.GetFirst must have the signature of pair.GetFirst
pair(x:type, y:type) := class:
    First:x
    Second:y
    GetFirst():x = First
swap(x:type, y:type) := class(pair(y, x)):
    Mine:x
    GetFirst<override>():x = Mine
Main():void =
    W := swap(int, string){First := "s", Second := 2, Mine := 9}
    P:pair(string, int) = W
    S:string = P.GetFirst()
    Print("{S.Length}")
    Print(S)
