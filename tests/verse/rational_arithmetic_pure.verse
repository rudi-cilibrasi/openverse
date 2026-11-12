Check(Tag:string,R:rational,N:int,D:int):void=
    if(E:=N/D,R=E)then Print("{Tag} {Floor(R)} {Ceil(R)}")else Print("bad {Tag}")
Add(A:rational,B:rational)<computes>:rational=A+B
Subtract(A:rational,B:rational)<computes>:rational=A-B
Multiply(A:rational,B:rational)<computes>:rational=A*B
Divide(A:rational,B:rational)<computes><decides>:rational=A/B
Negate(A:rational)<computes>:rational=-A
Main():void=
    Check("add",Add(2,3),5,1)
    Check("sub",Subtract(2,3),-1,1)
    Check("mul",Multiply(2,3),6,1)
    Check("neg",Negate(2),-2,1)
    if(R:=Divide[2,3])then Check("div",R,2,3)else Print("bad")
