Two(N:int):int=N|N+1
cell:=class{var N:int=0}
Write(H:cell,N:int)<writes>:int=block{set H.N=N;N}
base(t:type):=class:
    Get(H:cell,X:t,?N:int=0)<computes>:int=0
impl:=class(base(int)):
    Get<override>(H:cell,X:int,?N:int=Write(H,X))<computes>:int=N
Use(W:base(t),X:t,H:cell,Stop:logic where t:type)<transacts>:int=
    var Total:int=0
    defer:Print("source {Total} {H.N}")
    if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),N:=W.Get(H,X),set Total+=1,After:[]t=Concatenate()):
        # (the return in the branch: a return cannot leave the condition, a
        # failure context, the Book of Verse's tests, Reachability.versetest:12)
        if(Stop?)then return N
        Print("normal {N}")
    -1
Main():void=
    H:=cell{}
    Print("returned {Use(impl{},8,H,true)}")
    Print("normal return {Use(impl{},9,H,false)}")
