Check(Tag:string,R:rational,N:int,D:int):void=
    if(E:=N/D,R=E)then Print("{Tag} {Floor(R)} {Ceil(R)}")else Print("bad {Tag}")
Id(X:t where t:type)<computes>:t=X
Main():void=
    if(A:=(-2)/(-3),B:=5/(-7)):
        Check("add",A+B,-1,21)
        Check("sub",A-B,29,21)
        Check("mul",A*B,-10,21)
        Check("neg",-A,-2,3)
        Check("mixed-add-left",2+B,9,7)
        Check("mixed-add-right",A+2,8,3)
        Check("mixed-sub-left",2-B,19,7)
        Check("mixed-sub-right",A-2,-4,3)
        Check("mixed-mul-left",2*B,-10,7)
        Check("mixed-mul-right",A*2,4,3)
        Check("generic",1+Id(B),2,7)
        if(R:=A/B)then Check("div",R,-14,15)else Print("bad div")
        if(R:=2/B)then Check("mixed-div-left",R,-14,5)else Print("bad mixed-div-left")
        if(R:=A/2)then Check("mixed-div-right",R,1,3)else Print("bad mixed-div-right")
