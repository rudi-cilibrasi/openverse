# expect: expected int, found [][]int
A(X:t,N:int where t:type)<transacts>:int =
    Print("A")
    if(N>0)then(N|B(array{X},N-1))else 0
B(X:u,N:int where u:type)<transacts>:int =
    Print("B")
    if(N>0)then(N|A(array{X},N-1))else 0
Main():void = for(V:=A(7,2)): Print("{V}")
