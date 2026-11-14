buffer(t:type) := class:
    var Items:[]t = ()

    Add(X:t):void = set Items += array{X}

    Take()<decides>:t =
        Result := Items[0]
        set Items = for (I -> X : Items, I > 0) { X }
        Result

child_buffer(t:type) := class(buffer(t)) {}
frozen(t:type) := class<computes> { Items:[]t = () }

Make(Seed:t where t:type):buffer(t) = buffer(t){}

Main():void =
    A := Make(3)
    B := buffer(int){}
    Texts := buffer(string){}
    Child := child_buffer(int){}
    Print("start {A.Items.Length} {B.Items.Length} {Texts.Items.Length}")
    A.Add(3)
    A.Add(5)
    B.Add(9)
    Texts.Add("ok")
    Child.Add(7)
    Print("lengths {A.Items.Length} {B.Items.Length} {Texts.Items.Length} {Child.Items.Length}")
    if (V := A.Take[]) then Print("take {V}")
    Print("after {A.Items.Length} {B.Items.Length}")
    if (Text := Texts.Items[0]) then Print("text {Text}")
    Nested := buffer(buffer(int)){}
    Nested.Add(B)
    if (Inner := Nested.Items[0], N := Inner.Items[0]) then Print("nested {N}")
    Print("pure {frozen(int){}.Items.Length}")
