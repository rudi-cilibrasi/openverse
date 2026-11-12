# expect: declared construction budget
data:=class<reads>{Value:int}
Make(N:int)<computes>:data=data{Value:=N}
Capture()<computes>:type{_(:int)<computes>:data}=Make
Main():void={}
