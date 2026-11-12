# expect: declared construction budget
M:=module:
    data<public>:=struct<reads>{Value:int}
    Make<public>(N:int)<computes>:data=data{Value:=N}
Main():void={}
