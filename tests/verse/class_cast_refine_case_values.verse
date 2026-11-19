# Later arms and the default lift their own casts at an aggregate result
# type. The first arm needs no cast. Inference agrees with named controls.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){}
Direct(P:pair(a,b),N:int where a:type,b:type)<transacts><decides>:[]b=
    case(N):
        0 => array{P.B}
        1 => array{dup[P].A}
        _ => array{dup[P].B}
Named(P:pair(a,b),N:int where a:type,b:type)<transacts><decides>:[]b=
    case(N):
        0 => array{P.B}
        1 => (D:=dup[P];array{D.A})
        _ => (D:=dup[P];array{D.B})
Main():void=
    for(N:=0..2):
        if(V:=Direct[dup(int){A:=7,B:=9},N],W:=Named[dup(int){A:=7,B:=9},N],X:=V[0],Y:=W[0]) then Print("int {N} {X} {Y}") else Print("int fail")
        if(V:=Direct[dup(string){A:="left",B:="right"},N],W:=Named[dup(string){A:="left",B:="right"},N],X:=V[0],Y:=W[0]) then Print("string {N} {X} {Y}") else Print("string fail")
        if(V:=Direct[pair(int,string){A:=1,B:="other"},N],W:=Named[pair(int,string){A:=1,B:="other"},N],X:=V[0],Y:=W[0]) then Print("other {N} {X} {Y}") else Print("other fail")
