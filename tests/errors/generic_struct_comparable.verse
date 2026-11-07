# expect: type argument k of keyed must be comparable, and u is not: declare u:subtype(comparable)
keyed(k:subtype(comparable)) := struct:
    Key:k

Wrap(X:u where u:type):keyed(u) = keyed(u){Key := X}

Main():void = Print("x")
