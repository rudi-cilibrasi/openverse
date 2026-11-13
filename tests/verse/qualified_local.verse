# (local:) (Book of Verse ch. 16, "Local Qualifiers"): a local or a
# parameter qualified with (local:) may take the name of a definition
# outside the code; its uses write (local:) where that definition is
# visible too, and may be bare where it is not.
Store := module:
    Factor<public>:int = 7
    Limit<public>:int = 99
    Index<public>:int = 99
    Scale<public>((local:)Factor:int):int =
        (local:)Base:int = 10
        (local:)Base * (local:)Factor
    SumTo<public>((local:)Limit:int):int =
        var (local:)Total:int = 0
        for ((local:)Index := 0..(local:)Limit):
            set (local:)Total += (local:)Index
        (local:)Total
    Squares<public>(N:int):[]int =
        for ((local:)Index : array{1, 2, 3}, (local:)Index <= N):
            (local:)Index * (local:)Index
    Clamp<public>((local:)Limit:int, X:int):int =
        block:
            (local:)Factor:int = 2
            if ((local:)Factor * X > (local:)Limit) then (local:)Limit else (local:)Factor * X
    WithCode<public>:int = {(local:)Factor := 1; (local:)Factor + (Store:)Factor}
counter := class:
    var Value<public>:int = 0
    block:
        (local:)Value:int = 42
        set (counter:)Value = (local:)Value
SumOf(Xs:[]int):int =
    var T:int = 0
    for (X : Xs):
        set T += X
    T
# no definition outside is named so: a bare use means the local
Fact(N:int):int =
    var (local:)Result:int = 1
    for (I := 2..N):
        set Result *= I
    (local:)Result + (local:)N - N
Main():void =
    Print("{Store.Scale(3)} {Store.SumTo(4)} {SumOf(Store.Squares(2))} {Store.Clamp(5, 4)} {Store.WithCode}")
    Print("{counter{}.Value} {Fact(5)} {Store.Factor}")
