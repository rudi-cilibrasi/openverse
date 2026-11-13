# In <suspends> functions: a for whose first clause is a refining choice
# and whose next has a choice too, left by a break, in its clauses, of the loop it is in;
# and clauses copied once per alternative of a choice of values of
# different types, each with a for whose body returns from a refining
# cast's branch that waits: each copy's return slot is its own
pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Dup(X:t where t:type)<transacts>:t = X|X
Walk(P:pair(a,b) where a:type,b:type)<suspends>:int =
    var Total:int=0
    loop:
        Sleep(0.0)
        for(V0:=if(D:=dup[P])then(D.C|D.C+1)else 0,V1:=(V0|V0*10),set Total+=V1,if(Total>40)then break else 0):
            set Total+=100
        set Total+=1000
        if(Total>5000):
            break
    Total
Run(P:pair(a,b),Limit:int where a:type,b:type)<suspends>:string =
    var N:int=0
    for(A:=(Dup(1)|Dup("s"))):
        for(I:=0..Limit):
            if(D:=dup[P]):
                Sleep(0.0)
                set N+=1
                if(N=Limit+3):
                    return "{A} {I} {D.C} {N}"
    "none {N}"
Main()<suspends>:void=
    Y:pair(int,int)=dup(int){A:=1,B:=2}
    Z:pair(int,int)=pair(int,int){A:=1,B:=2}
    Print("{Walk(Y)} {Walk(Z)}")
    Print("{Run(Y,3)}, {Run(Y,0)}, {Run(Z,3)}")
