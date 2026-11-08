# subclasses sharing an override but fixing more type arguments (#142)
pair(t:type, u:type) := class:
    A:t
    B:u
    Describe():string = "pair"
    Second():u = B
pair_int(u:type) := class(pair(int, u)):
    Describe<override>():string = "pair_int {A}"
pair_int_str := class(pair_int(string)):
    Extra:int = 0
pair_int_logic := class(pair_int(logic)):
    Second<override>():logic = false
Show(P:pair(t, u) where t:type, u:type):string = P.Describe()
SecondOf(P:pair(t, u) where t:type, u:type):u = P.Second()
SecondInt(P:pair(int, u) where u:type):u = P.Second()
Main():void =
    Print(Show(pair_int(int){A := 1, B := 2}))
    Print(Show(pair_int_str{A := 3, B := "x"}))
    Print(Show(pair_int_logic{A := 4, B := true}))
    Print(Show(pair(string, string){A := "a", B := "b"}))
    Print(SecondOf(pair_int_str{A := 3, B := "x"}))
    if (SecondOf(pair_int_logic{A := 4, B := true})?) then Print("true") else Print("false")
    Print("{SecondOf(pair_int(int){A := 1, B := 2})}")
    Print(SecondInt(pair_int_str{A := 3, B := "y"}))
    if (SecondInt(pair_int_logic{A := 4, B := true})?) then Print("true") else Print("false")
