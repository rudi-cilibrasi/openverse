# function values by variance (#214): a comparable generic function at a
# closed type, with an unrelated closed type written elsewhere; a generic
# function at a function-typed parameter and at string (as []char); a
# parametric struct's function-typed field
animal := class:
    Name:string
Same(X:t where t:subtype(comparable)):t = X
Keep(F:type{_(:animal):animal}, A:animal):animal = F(A)
UseI(F:int->int):int = F(5)
Apply(F:type{_(:t):t}, X:t where t:type):t = F(X)
UseA(F:type{_(:int->int, :int):int}):int = F(UseI2, 1)
UseI2(X:int):int = X + 1
Len(X:[]t where t:type):int = X.Length
UseS(F:type{_(:string):int}):int = F("abcd")
pair(t:type) := struct:
    F:type{_(:t):t}
Id(X:t where t:type):t = X
Main():void =
    Print("{UseI(Same)}")
    Print(Keep(Id, animal{Name := "a"}).Name)
    Print("{UseA(Apply)} {UseS(Len)}")
    P := pair(int){F := UseI2}
    Print("{P.F(9)}")
