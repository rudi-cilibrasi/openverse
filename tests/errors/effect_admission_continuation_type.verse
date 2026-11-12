# expect: <predicts>
Count():int=1
Main():void=
    for(X:=1|2):
        F:type{_()<predicts>:int}=Count
        Print("{X} {F()}")
