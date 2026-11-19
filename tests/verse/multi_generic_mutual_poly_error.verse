# The eager compatibility path still reaches errors after an earlier value.
# (the error: ToString of an int beyond 64 bits, #724)
A(X:t,N:int where t:type)<computes>:int =
    if(N>0)then(7|B(array{X},N-1))else ToString(9223372036854775807+1).Length
B(X:u,N:int where u:type)<computes>:int =
    if(N>0)then(7|A(array{X},N-1))else ToString(9223372036854775807+1).Length
Main():void =
    Print("start")
    if(V:=A(7,1))then Print("unexpected")
