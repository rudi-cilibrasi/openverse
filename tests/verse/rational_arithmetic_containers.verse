Check(Tag:string,R:rational,N:int,D:int):void=
    if(E:=N/D,R=E)then Print("{Tag} {Floor(R)} {Ceil(R)}")else Print("bad {Tag}")
Main():void=
    if(A:=1/2,B:=1/3):
        K:=A+B
        M:[rational]int=map{K=>7}
        if(E:=5/6,V:=M[E])then Print("key {V}")else Print("bad")
        R:=for(X:=A+B|A-B):X*2
        for(X:R):Print("value {Floor(X)} {Ceil(X)}")
