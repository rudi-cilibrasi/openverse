# expect: declared construction budget
box(t:type):=struct<reads>{Value:t}
Build(N:int)<computes>:int=box(int){Value:=N|N+1}.Value
Main():void={}
