# expect: 3:14: 't' is already defined (as a type alias); Verse does not allow shadowing
t := int
Id(X:t1 where t:type, t1:type):t1 = X
Main():void = {}
