# a struct type argument that the struct's fields do not mention, in a pin:
# the refinement is Verse Core's, which compares the struct by its fields (#209)
tag(t:type) := struct:
    N:int = 0
pair(t:type, u:type) := class:
    A:t
    B:u
    Name():string = "pair"
c(t:type) := class(pair(t, tag(t))):
    Name<override>():string = "c"
F(P:pair(a, tag(int)) where a:type):string = P.Name()
Main():void =
    Print(F(c(int){A := 1, B := tag(int){}}))
    Print(F(pair(string, tag(int)){A := "s", B := tag(int){}}))
