# expect: would name what is unknown (#250)
base(t:type):=class{Value:t}
pair(t:type,u:type):=class(base(t)){Other:u}
Empty(?Default:?t=false where t:type)<transacts>:?t=Default
Key(V:?int)<transacts>:?int=V
Main():void=
    B:base(int)=pair(int,string){Value:=1,Other:="other"}
    X:=option{map{Key(Empty())=>option{pair[B].Other}}}
