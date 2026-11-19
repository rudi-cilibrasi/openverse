shared := interface{}
alpha := class(shared){}
beta := class(shared){}

F(X:[]shared):void =
    Print("OVPROBE length {X.Length}")

Main():void =
    F(array{alpha{}, beta{}})
