Two(N:int):int = N|N+1
pair(t:type,u:type) := class { A:t;B:u }
dup(t:type) := class(pair(t,t)) {}
container(t:type) := interface:
    Get()<suspends>:int
pinned(t:type,u:type) := interface(container([]t)):
    R():pair(u,int)
    Get<override>()<suspends>:int =
        var Total:int=0
        for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2))):
            if(D:=dup[R()]) then set Total+=1 else set Total+=10
        Total
fixed(a:type) := class(pinned(a,string)):
    R<override>():pair(string,int)=pair(string,int){A:="s",B:=1}
same(a:type) := class(pinned(a,int)):
    R<override>():pair(int,int)=dup(int){A:=1,B:=2}
Main()<suspends>:void =
    Print("{fixed(int){}.Get()} {same(string){}.Get()}")
