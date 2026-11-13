# In <suspends> functions: clauses copied once per alternative of a choice
# of values of different types, each with a for whose body returns from a
# refining cast's branch that waits: each copy's return slot is its own.
# (A for whose first clause is a refining choice, left by a break in its
# clauses, is gone: a break cannot leave a for's clauses, a failure context,
# the Book of Verse's tests, SOL-4199-BreakFromIf.versetest:15.)
pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Dup(X:t where t:type)<transacts>:t = X|X
Run(P:pair(a,b),Limit:int where a:type,b:type)<suspends>:string =
    var N:int=0
    for(A:=(Dup(1)|Dup("s"))):
        for(I:=0..Limit):
            if(D:=dup[P]):
                Sleep(0.01)
                set N+=1
                if(N=Limit+3):
                    return "{A} {I} {D.C} {N}"
    "none {N}"
Main()<suspends>:void=
    Y:pair(int,int)=dup(int){A:=1,B:=2}
    Z:pair(int,int)=pair(int,int){A:=1,B:=2}
    Print("{Run(Y,3)}, {Run(Y,0)}, {Run(Z,3)}")
