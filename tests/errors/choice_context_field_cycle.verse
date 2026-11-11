# expect: the default of field 'Value' of a depends on itself
Two(N:int):int=N|N+1
a:=struct:
    Value:int=block:
        R:=for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2))):b{}.Value
        R.Length
b:=struct{Value:int=a{}.Value}
Main():void=Print("{a{}.Value}")
