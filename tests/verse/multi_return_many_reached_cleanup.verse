F(N:int)<transacts>:int=
    defer:Print("outer {N}")
    if(N=-9001):return N
    if(N=-9002):return N
    if(N=-9003):return N
    if(N=-9004):return N
    if(N=-9005):return N
    if(N=-9006):return N
    if(N=-9007):return N
    if(N=-9008):return N
    if(N=-9009):return N
    if(N=-9010):return N
    if(N=-9011):return N
    if(N=-9012):return N
    if(N=-9013):return N
    if(N=-9014):return N
    if(N=-9015):return N
    if(N=-9016):return N
    if(N=-9017):return N
    if(N=-9018):return N
    if(N=0):
        defer:Print("inner")
        return 10|11
    defer:Print("late")
    20|21
Main()<transacts>:void=for(N:array{0,1}){for(V:=F(N)){Print("v {V}")}}
