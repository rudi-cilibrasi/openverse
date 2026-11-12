small:=type{_X:int where 0<=_X,_X<=10}
negative:=type{_X:int where -10<=_X,_X<=0}
fsmall:=type{_X:float where 0.0<=_X,_X<=10.0}
Ints(X:t,Y:u where t:subtype(int),u:subtype(int))<computes>:tuple(int,int,int,int,int,int,int)=(X+Y,X-Y,X*Y,-X,Abs(-X),Min(X,Y),Max(X,Y))
Divide(X:t,Y:u where t:subtype(int),u:subtype(int))<computes><decides>:rational=X/Y
Floats(X:t,Y:u where t:subtype(float),u:subtype(float))<computes>:tuple(float,float,float,float,float)=(X+Y,X-Y,X*Y,X/Y,-X)
Extras(X:t,Y:u where t:subtype(float),u:subtype(float))<computes>:tuple(float,float,float)=(Abs(-X),Min(X,Y),Max(X,Y))
Mixed(X:t,Y:u where t:subtype(int),u:subtype(float))<computes>:float=X*Y
Rats(X:t,Y:u where t:subtype(rational),u:subtype(rational))<computes>:tuple(rational,rational,rational)=(X+Y,X-Y,X*Y)
RatDivide(X:t,Y:u where t:subtype(rational),u:subtype(rational))<computes><decides>:rational=X/Y
FloorFloat(X:t where t:subtype(float))<computes><decides>:int=Floor[X]
RoundDiv(X:t,Y:u where t:subtype(int),u:subtype(int))<computes><decides>:tuple(int,int)=(Floor(X/Y),Ceil(X/Y))
Quo(X:t,Y:u where t:subtype(int),u:subtype(int))<computes><decides>:int=Quotient[X,Y]
Modular(X:t,Y:u where t:subtype(int),u:subtype(int))<computes><decides>:int=Mod[X,Y]
Refined(X:t where t:subtype(small))<computes>:int=-X+1
NegSmall(X:t where t:subtype(small))<computes>:negative=-X
RefinedFloat(X:t where t:subtype(fsmall))<computes>:float=-X+1.0
Less(X:t,Y:u where t:subtype(int),u:subtype(int))<computes><decides>:t=X<Y
Between(X:t,Y:u,Z:v where t:subtype(int),u:subtype(int),v:subtype(int))<computes><decides>:t=X<Y<Z
Equal(X:t,Y:u where t:subtype(int),u:subtype(int))<computes><decides>:t=X=Y
FloatLess(X:t,Y:u where t:subtype(float),u:subtype(float))<computes><decides>:t=X<Y
FloatLe(X:t,Y:u where t:subtype(float),u:subtype(float))<computes><decides>:t=X<=Y
RatLess(X:t,Y:u where t:subtype(rational),u:subtype(rational))<computes><decides>:t=X<Y
Main():void=
    I:=Ints(7,2)
    Print("ints {I(0)} {I(1)} {I(2)} {I(3)} {I(4)} {I(5)} {I(6)}")
    if(D:=Divide[7,2])then Print("divide {Floor(D)} {Ceil(D)}")
    if(Divide[7,0])then Print("bad")else Print("zero fails")
    F:=Floats(7.5,2.5)
    E:=Extras(7.5,2.5)
    Print("floats {F(0)} {F(1)} {F(2)} {F(3)} {F(4)}")
    Print("extras {E(0)} {E(1)} {E(2)} mixed {Mixed(3,2.5)}")
    if(Half:=7/2):
        R:=Rats(Half,2)
        Print("rats {Floor(R(0))} {Ceil(R(1))} {Floor(R(2))}")
        if(D:=RatDivide[Half,2])then Print("rat divide {Floor(D)} {Ceil(D)}")
        if(V:=RatLess[Half,4])then Print("rat comparison {Floor(V)}")
    if(FloorN:=FloorFloat[7.5],Q:=Quo[7,2],M:=Modular[7,2],D:=RoundDiv[7,2])then Print("builtins {FloorN} {Q} {M} {D(0)} {D(1)}")
    S:small=5
    SmallFloat:fsmall=4.0
    Print("refined {Refined(S)} {NegSmall(S)} {RefinedFloat(SmallFloat)}")
    if(V:=Less[S,9]):
        Kept:small=V
        Print("precise {Kept}")
    if(V:=Between[S,7,9]):
        Kept:small=V
        Print("chain {Kept}")
    if(V:=Equal[S,S]):
        Kept:small=V
        Print("equal {Kept}")
    if(V:=FloatLess[1.0,2.0])then Print("float comparison {V}")
    if(FloatLe[NaN,NaN],not FloatLess[NaN,NaN])then Print("nan ordering")
    Zero:=Floats(1.0,0.0)
    if(not IsFinite[Zero(3)])then Print("float zero")
