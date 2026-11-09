# function values (#231), review cases: a decides value reshaped from a
# tuple parameter still fails; `[]char` and `string` are one type in a
# method's variant; a generic function's single parameter unflattened
# at an instance
Check(P:tuple(int, int))<decides>:int = P(0) > P(1)
holder := class:
    Count(S:[]char):int = S.Length
Id(X:t where t:type):t = X
Main():void =
    F:type{_(:int, :int)<decides>:int} = Check
    if (R := F[7, 3]) then Print("{R}") else Print("failed")
    if (R := F[3, 7]) then Print("{R}") else Print("failed")
    O := holder{}
    G:type{_(:string):rational} = O.Count
    Print("{Floor(G("abc"))}")
    H:type{_(:int, :string):tuple(int, string)} = Id
    R := H(1, "a")
    Print("{R(0)} {R(1)}")
