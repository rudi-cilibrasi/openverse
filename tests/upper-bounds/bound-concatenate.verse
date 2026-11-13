car:=class<computes>{Name:string="precise"}
Flatten(A:t where t:subtype([][]int))<computes>:[]int=(R:=Concatenate(A);R)
Elements(A:[]a where a:subtype([]int))<computes>:[]int=(R:=Concatenate(A);R)
Composed(A:t,Seed:a where a:subtype([]int),t:subtype([]a))<computes>:[]int=(R:=Concatenate(A);R)
Precise(A:t,Seed:e where e:type,a:subtype([]e),t:subtype([]a))<computes>:[]e=(R:=Concatenate(A);R)
Several(A:t,B:u where t:subtype([]int),u:subtype([]int))<computes>:[]int=(R:=Concatenate(A,B,array{9});R)
Words(A:[]a where a:subtype(string))<computes>:string=(R:=Concatenate(A);R)
Main():void=
    A:=array{array{1,2},array{3}}
    F:=Flatten(A)
    E:=Elements(A)
    C:=Composed(A,array{0})
    if(X:=F[2],Y:=E[1],Z:=C[0])then Print("flatten {F.Length} {X} elements {Y} composed {Z}")
    Empty:[][]int=array{}
    Print("empty {Flatten(Empty).Length}")
    S:=Several(array{1},array{2,3})
    if(X:=S[0],Y:=S[2],Z:=S[3])then Print("several {S.Length} {X} {Y} {Z}")
    V:=car{}
    P:=Precise(array{array{V}},V)
    if(X:=P[0])then Print("precise {X.Name}")
    Print("words {Words(array{"ab","cd"})}")
