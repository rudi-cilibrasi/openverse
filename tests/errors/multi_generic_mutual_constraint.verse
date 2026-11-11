# expect: must be comparable
A(X:t,N:int where t:type)<transacts>:t =
    Print("A")
    if(N>0)then(X|B(X,N-1))else X
B(X:u,N:int where u:subtype(comparable))<transacts>:u =
    if(N>0)then(X|A(X,N-1))else X
Main():void = for(V:=A(7,2)): Print("{V}")
