# A cast that opens a type argument the object's type does not name (#250):
# pair's u, for a base(int); its branch reads the object's fields
base(t:type) := class:
    Value:t
pair(t:type, u:type) := class(base(t)):
    Other:u
Main():void =
    B:base(int) = pair(int, string){Value := 1, Other := "o"}
    if (P := pair[B]) then Print("pair {P.Value}")
    C:base(int) = base(int){Value := 2}
    if (P := pair[C]) then Print("pair {P.Value}") else Print("not a pair")
