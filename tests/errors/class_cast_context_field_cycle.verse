# expect: the default of field
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
root:=class{}
extra(t:type):=class(root){X:t}
Global:root=extra(int){X:=7}
alpha:=struct{Value:int=if(D:=extra[Global])then block{R:=for(V:=(1|2)):beta{}.Value;R.Length}else 0}
beta:=struct{Value:int=alpha{}.Value}
Main():void=Print("{alpha{}.Value}")
