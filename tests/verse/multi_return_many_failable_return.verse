Positive(N:int)<computes><decides>:int={N>0;N}
F(N:int)<computes><decides>:int=
    if(N=-9001)then return Positive[N]else if(N=-9002)then return Positive[N]else if(N=-9003)then return Positive[N]else if(N=-9004)then return Positive[N]else if(N=-9005)then return Positive[N]else if(N=-9006)then return Positive[N]else if(N=-9007)then return Positive[N]else if(N=-9008)then return Positive[N]else if(N=-9009)then return Positive[N]else if(N=-9010)then return Positive[N]else if(N=-9011)then return Positive[N]else if(N=-9012)then return Positive[N]else if(N=-9013)then return Positive[N]else if(N=-9014)then return Positive[N]else if(N=-9015)then return Positive[N]else if(N=-9016)then return Positive[N]else if(N=-9017)then return Positive[N]else if(N=-9018)then return Positive[N]else if(N<1)then return Positive[N]else return(N|N+1)
Main():void=
    if(V:=F[-1])then Print("v {V}")else Print("none")
    for(V:=F[2]){Print("v {V}")}
