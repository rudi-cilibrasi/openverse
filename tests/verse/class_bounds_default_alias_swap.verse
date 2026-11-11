# Comparable facts from a selected class case remain local to that case (#209).
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
plain := class { N:int }
F(A:u,B:t,?Q:[]u=block{V:[]u=Concatenate(); W:[]t=Concatenate(); if(V=V) then V else V} where t:type,u:subtype(comparable)):u = A
Run(A:t,B:u where t:subtype(comparable),u:type):t = F(A,B)
Main():void =
    Print("{Run(7,plain{N:=1})}")
    Print(Run("s",plain{N:=2}))
