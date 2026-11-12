# expect: expected int, found tuple(string, string)
NeedsInt(X:int):int=X
F(X:string):string=X
F(X:int,Y:int):int=X+Y
Main():void=Print(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(F(NeedsInt(("bad","pair")))))))))))))))))))))))))))
