# Zero accepted suffix rows undo the complete search; source exits keep committed work.

expr(t:type):=class<abstract>{Eval()<transacts>:t}
lit:=class(expr(int)){V:int;Eval<override>()<transacts>:int=V}
vpair(a:type,b:type):=class(expr(tuple(a,b))){var L:expr(a);R:expr(b);Eval<override>()<transacts>:tuple(a,b)=(L.Eval(),R.Eval())}

Run0(E:expr(t) where t:type)<transacts><decides>:[]t=
    for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>2):
        (L.V,R.V)
Case0()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(Rows:=Run0[E])then Print("rows {Rows.Length}")else Print("failure")
    Print("state {E.L.Eval()}")

Run1(E:expr(t) where t:type)<transacts><decides>:[]t=
    for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N=2):
        (L.V,R.V)
Case1()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(Rows:=Run1[E])then Print("rows {Rows.Length}")else Print("failure")
    Print("state {E.L.Eval()}")

Run2(E:expr(t) where t:type)<transacts><decides>:[]t=
    for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>0):
        (L.V,R.V)
Case2()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(Rows:=Run2[E])then Print("rows {Rows.Length}")else Print("failure")
    Print("state {E.L.Eval()}")

Reject3()<transacts><decides>:void=false?
Run3(E:expr(t) where t:type)<transacts><decides>:[]t=
    for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>0):
        Reject3[]
        (L.V,R.V)
Case3()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(Rows:=Run3[E])then Print("rows {Rows.Length}")else Print("failure")
    Print("state {E.L.Eval()}")

Run4(E:expr(t) where t:type)<transacts><decides>:[][]t=
    for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>0):
        if(N=1)then array{(L.V,R.V)}else array{}
Case4()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(Rows:=Run4[E])then Print("rows {Rows.Length}")else Print("failure")
    Print("state {E.L.Eval()}")

Run5(E:expr(t) where t:type)<transacts><decides>:t=first{P:=vpair[E];Saved:=P.L;L:=lit[Saved];Changed:=block{Print("prefix");set P.L=lit{V:=99};1};R:=lit[P.R];N:=1..2;N>2;(L.V,R.V)}
Case5()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(V:=Run5[E])then Print("value {V(0)} {V(1)}")else Print("failure")
    Print("state {E.L.Eval()}")

Run6(E:expr(t) where t:type)<transacts><decides>:t=first{P:=vpair[E];Saved:=P.L;L:=lit[Saved];Changed:=block{Print("prefix");set P.L=lit{V:=99};1};R:=lit[P.R];N:=1..2;N>0;(L.V,R.V)}
Case6()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(V:=Run6[E])then Print("value {V(0)} {V(1)}")else Print("failure")
    Print("state {E.L.Eval()}")

Run7(E:expr(t) where t:type)<transacts>:?t=option{P:=vpair[E];Saved:=P.L;L:=lit[Saved];Changed:=block{Print("prefix");set P.L=lit{V:=99};1};R:=lit[P.R];N:=(1|2);N>2;(L.V,R.V)}
Case7()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(V:=Run7(E)?)then Print("value {V(0)} {V(1)}")else Print("failure")
    Print("state {E.L.Eval()}")

Run8(E:expr(t) where t:type)<transacts>:?t=option{P:=vpair[E];Saved:=P.L;L:=lit[Saved];Changed:=block{Print("prefix");set P.L=lit{V:=99};1};R:=lit[P.R];N:=(1|2);N>0;(L.V,R.V)}
Case8()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(V:=Run8(E)?)then Print("value {V(0)} {V(1)}")else Print("failure")
    Print("state {E.L.Eval()}")

Run9(E:expr(t) where t:type)<transacts>:[]t=
    Ignored:[]t=for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>0):
        Print("body")
        if(N=1)then return array{}
        (L.V,R.V)
    array{}
Case9()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    Rows:=Run9(E)
    Print("rows {Rows.Length}")
    Print("state {E.L.Eval()}")

Run10(E:expr(t) where t:type)<transacts><decides>:[]t=
    for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{defer{Print("cleanup")};Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>2):
        (L.V,R.V)
Case10()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(Rows:=Run10[E])then Print("rows {Rows.Length}")else Print("failure")
    Print("state {E.L.Eval()}")

Run11(E:expr(t) where t:type)<transacts><decides>:[]t=
    for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{defer{Print("cleanup")};Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>0):
        (L.V,R.V)
Case11()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(Rows:=Run11[E])then Print("rows {Rows.Length}")else Print("failure")
    Print("state {E.L.Eval()}")

Run12(E:expr(t) where t:type)<transacts><decides>:tuple([]t,int)=
    var Count:int=0
    Rows:[]t=for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{defer{set Count+=1};set Count+=1;Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>2):
        (L.V,R.V)
    (Rows,Count)
Case12()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(Result:=Run12[E])then Print("rows {Result(0).Length} count {Result(1)}")else Print("failure")
    Print("state {E.L.Eval()}")

Run13(E:expr(t) where t:type)<transacts><decides>:tuple([]t,int)=
    var Count:int=0
    Rows:[]t=for(P:=vpair[E],Saved:=P.L,L:=lit[Saved],Changed:=block{defer{set Count+=1};set Count+=1;Print("prefix");set P.L=lit{V:=99};1},R:=lit[P.R],N:=1..2,N>0):
        (L.V,R.V)
    (Rows,Count)
Case13()<transacts>:void=
    E:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=7}}
    if(Result:=Run13[E])then Print("rows {Result(0).Length} count {Result(1)}")else Print("failure")
    Print("state {E.L.Eval()}")

Main()<transacts>:void=
    Print("zero")
    Case0()
    Print("one")
    Case1()
    Print("some")
    Case2()
    Print("body-failure")
    Case3()
    Print("array-valued-body")
    Case4()
    Print("first-2")
    Case5()
    Print("first-0")
    Case6()
    Print("option-2")
    Case7()
    Print("option-0")
    Case8()
    Print("return-empty-value")
    Case9()
    Print("cleanup-2")
    Case10()
    Print("cleanup-0")
    Case11()
    Print("copyout-2")
    Case12()
    Print("copyout-0")
    Case13()
