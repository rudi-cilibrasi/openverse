# expect: map key must be comparable
holder(a:type) := class:
    Value:a
    Pick(Key:b where b:subtype(comparable))<transacts>:int =
        M:[a]int=map{Value=>1}
        1|2
Main():void = for(V:=holder(int){Value:=7}.Pick("key")): Print("{V}")
