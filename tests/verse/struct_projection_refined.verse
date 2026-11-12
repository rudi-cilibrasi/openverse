# Construction under opened and unified GADT types needs no typed local.
pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) {}
box(t:type) := struct<computes> { E:[]t=Concatenate(); V:t }
Read(X:t where t:type)<computes>:t = box(t){V:=X}.V
Run(P:pair(a,b) where a:type,b:type):void =
    for(V:=if(D:=dup[P])then (box(a){V:=D.A|D.B}.E.Length | Read(7))else box(b){V:=P.B|P.B}.E.Length):
        Print("refined {V}")
Main():void =
    Run(dup(int){A:=1,B:=2})
    Run(pair(int,string){A:=1,B:="s"})
