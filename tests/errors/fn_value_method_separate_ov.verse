# expect: c implements M separately for ia and ib, so the value M would not say which
# (also when a class below overloads M, which renames it, #106)
ia := interface:
    M(X:int):int
ib := interface:
    M(X:int):int
c := class(ia, ib):
    (ia:)M<override>(X:int):int = 1
    (ib:)M<override>(X:int):int = 2
d := class(c):
    M(X:string):string = X
Run(F:type{_(:int):int}):int = F(0)
Main():void =
    X := c{}
    Print("{Run(X.M)}")
