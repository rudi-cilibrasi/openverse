# expect: would name what is unknown (#250)
base(t:type):=class{Value:t}
pair(t:type,u:type):=class(base(t)){Other:u;Lo:int=0;Hi:int=1}
Add(X:int,Y:int):int=X+Y
Main():void=
    B:base(int)=pair(int,string){Value:=1,Other:="o"}
    X:=for(I:=Add(pair[B].Lo,pair[B].Lo)..2){(I,option{pair[B].Other})}
    Print("{X.Length}")
