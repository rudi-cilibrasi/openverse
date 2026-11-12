# expect: effect <reads>
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){}
Two(N:int)<computes>:int=N|N+1
Pure(P:pair(a,b) where a:type,b:type)<computes>:float=
    if(D:=dup[P]):
        R:=for(V:=(Two(0)|Two(2)),W:=(Two(0)|Two(2))):Sinh(0.0)
        R[0] or 0.0
    else:0.0
Main():void=Print("{Pure(dup(int){})}")
