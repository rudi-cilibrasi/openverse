pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Run(P:pair(a,b) where a:type,b:type):void=
    defer:Print("{block{R:=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):V;R.Length}}")
    Print("body")
Main():void=Run(dup(int){})
