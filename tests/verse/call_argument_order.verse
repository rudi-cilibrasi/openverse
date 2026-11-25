# Packed positional fields precede written names, selected defaults and body.
# (#724: beside a named parameter the tuple is written out: Epic's compiler packs no
# several arguments into a tuple parameter there, UEFN 43.12 error 3509,
# followup-book2/overload-tuple-named-call)
state:=class:
    var N:int=0
Mark(S:state,Name:string,V:int)<transacts>:int=
    set S.N+=1
    Print("{Name} {S.N}")
    V
F(S:state,P:tuple(int,int),?B:int,?A:int,?D:int=Mark(S,"D",P(0)+A),?E:int=Mark(S,"E",P(1)+B))<decides>:int=
    Print("body {D+E}")
    D+E
# The sole positional formal is a nested tuple; fields stay nested.
G(P:tuple(state,tuple(int,int)),?B:int,?A:int,?D:int=Mark(P(0),"D",P(1)(0)+A),?E:int=Mark(P(0),"E",P(1)(1)+B))<transacts><decides>:int=
    Print("body {D+E}")
    D+E
Main():void=
    S:=state{}
    if(R:=G[(S,(Mark(S,"left",1),Mark(S,"right",2))),?B:=Mark(S,"B",3),?A:=Mark(S,"A",4)],false?){Print("unreachable")}
    Print("after {S.N}")
    if(R:=G[(S,(Mark(S,"left",1),Mark(S,"right",2))),?B:=Mark(S,"B",3),?A:=Mark(S,"A",4)]){Print("result {R} {S.N}")}
