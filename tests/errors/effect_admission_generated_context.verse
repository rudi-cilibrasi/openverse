# expect: <predicts>
root(t:type):=class{}
leaf:=class(root(int)){}
Use(B:root(t) where t:type):void=
    if(D:=leaf[B]):
        F:type{_()<predicts>:int}=Count
        Print("{F()}")
Count():int=1
Main():void={}
