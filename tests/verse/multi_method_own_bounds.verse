# A method's comparable bound applies to its key, independently of the class.
data := class { N:int }
identity := class<unique> {}
store(a:type) := class:
    Value:a
    Table(Key:b where b:subtype(comparable))<transacts>:tuple(a,b) =
        M:[b]a=map{Key=>Value}
        (Value,Key)|(Value,Key)
sub(u:type) := class(store(u)):
    Table<override>(Key:v where v:subtype(comparable))<transacts>:tuple(u,v) =
        M:[v]u=map{Key=>Value}
        (Value,Key)|(super:)Table(Key)
Main():void =
    S:store(data)=sub(data){Value:=data{N:=7}}
    for(V:=S.Table("key")): Print("value {V(0).N} {V(1)}")
    K:=identity{}
    for(V:=S.Table(K)):
        if(V(1)=K)then Print("identity {V(0).N}")
