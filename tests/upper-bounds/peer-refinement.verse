small:=type{_X:int where 0 <= _X, _X <= 10}
wide:=type{_X:int where -10 <= _X, _X <= 20}
fsmall:=type{_X:float where 0.0 <= _X, _X <= 10.0}
Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Choose(X:u,Y:v where t:type,u:subtype(t),v:subtype(t))<computes>:t=X
Process(X:t where t:subtype(wide))<computes>:t=X
Same(X:t,Y:t where t:subtype(wide))<decides>:t=X=Y
holder(t:subtype(wide)):=class<computes>:
    Value:t
    Get()<computes>:t=Value
Main():void=
    S:small=7
    N:=Upper(0,S)
    Print("refinement {N}")
    R:rational=0
    Rat:=Upper(R,S)
    if(Rat=7):Print("refined rational 7")
    W:wide=0
    Wider:=Upper(W,S)
    Print("interval {Wider}")
    Precise:small=Process(S)
    Print("precise {Precise}")
    if(E:=Same[S,S]):Print("refined comparable {E}")
    H:=holder(small){Value:=S}
    Held:small=H.Get()
    Print("refined holder {Held}")
    F:fsmall=2.5
    G:=Upper(0.0,F)
    if(G=2.5):Print("refined float 2.5")
    I:=Choose(S,0)
    Print("inferred refinement {I}")
    J:=Choose(S,W)
    Print("inferred interval {J}")
