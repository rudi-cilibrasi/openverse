small:=type{_X:int where 0<=_X,_X<=10}
negative:=type{_X:int where -10<=_X,_X<=0}
fsmall:=type{_X:float where 0.0<=_X,_X<=10.0}
Ints(X:int,Y:int)<computes>:tuple(int,int,int,int,int,int,int)=(X+Y,X-Y,X*Y,-X,Abs(-X),Min(X,Y),Max(X,Y))
Divide(X:int,Y:int)<computes><decides>:rational=X/Y
Floats(X:float,Y:float)<computes>:tuple(float,float,float,float,float)=(X+Y,X-Y,X*Y,X/Y,-X)
Extras(X:float,Y:float)<computes>:tuple(float,float,float)=(Abs(-X),Min(X,Y),Max(X,Y))
Mixed(X:int,Y:float)<computes>:float=X*Y
Rats(X:rational,Y:rational)<computes>:tuple(rational,rational,rational)=(X+Y,X-Y,X*Y)
RatDivide(X:rational,Y:rational)<computes><decides>:rational=X/Y
FloorFloat(X:float)<computes><decides>:int=Floor[X]
RoundDiv(X:int,Y:int)<computes><decides>:tuple(int,int)=(Floor(X/Y),Ceil(X/Y))
Quo(X:int,Y:int)<computes><decides>:int=Quotient[X,Y]
Modular(X:int,Y:int)<computes><decides>:int=Mod[X,Y]
Refined(X:small)<computes>:int=-X+1
NegSmall(X:small)<computes>:negative=-X
RefinedFloat(X:fsmall)<computes>:float=-X+1.0
Less(X:small,Y:int)<computes><decides>:small=(X<Y;X)
Between(X:small,Y:int,Z:int)<computes><decides>:small=(X<Y<Z;X)
Equal(X:small,Y:small)<computes><decides>:small=(X=Y;X)
FloatLess(X:float,Y:float)<computes><decides>:float=X<Y
FloatLe(X:float,Y:float)<computes><decides>:float=X<=Y
RatLess(X:rational,Y:rational)<computes><decides>:rational=X<Y
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
