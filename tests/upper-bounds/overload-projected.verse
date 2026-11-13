root(a:type):=class<computes>{}
leaf(a:type):=class<computes>(root(a)){}
F(X:t where t:subtype(root(int)))<computes>:int=1
F(X:t where t:subtype(root(string)))<computes>:int=2
Main():void=Print("projected {F(leaf(int){})} {F(leaf(string){})}")
