# expect: 3:13: 't' is already defined (as a type alias); Verse does not allow shadowing
t := int
Id(X:t where t:type):t = X
Main():void = {}
