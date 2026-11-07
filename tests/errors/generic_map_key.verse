# expect: a map key must be comparable, and t is not: declare t:subtype(comparable)
Count(M:[t]int where t:type):int = M.Length

Main():void = Print("x")
