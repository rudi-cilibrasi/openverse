# a class fixing one of two type arguments, and a failable override (#142)
pair(t:type, u:type) := class:
    A:t
    B:u
    Describe():string = "pair"
    First()<transacts><decides>:t = A
pair_int(u:type) := class(pair(int, u)):
    Describe<override>():string = "pair_int {A}"
    First<override>()<transacts><decides>:int =
        A > 0
        A
Show(P:pair(t, u) where t:type, u:type):string = P.Describe()
FirstOf(P:pair(t, u), D:t where t:type, u:type):t =
    if (X := P.First[]) then X else D
Main():void =
    Print(Show(pair_int(string){A := 3, B := "x"}))
    Print(Show(pair(string, int){A := "s", B := 1}))
    Print("{FirstOf(pair_int(logic){A := 5, B := true}, 0)}")
    Print("{FirstOf(pair_int(logic){A := -5, B := true}, 0)}")
    Print(FirstOf(pair(string, int){A := "f", B := 2}, "d"))
