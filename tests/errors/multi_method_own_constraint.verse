# expect: must be comparable
thing := class {}
picker := class:
    Pick(X:t where t:subtype(comparable))<transacts>:t =
        M:[t]int=map{X=>1}
        X|X
Main():void = for(V:=picker{}.Pick(thing{})): Print("unexpected")
