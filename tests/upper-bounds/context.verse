root(v:type):=class<computes>{Value:v}
leaf(v:type):=class<computes>(root(v)){}
Read(X:u,Y:[]a where a:type,u:subtype(root(a)))<computes>:[]a=array{X.Value}
Main():void=
    R:[]any=Read(leaf(int){Value:=17},array{})
    Print("context {R.Length}")
