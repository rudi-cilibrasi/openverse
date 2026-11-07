# expect: <computes> excludes the heap effects
Id(X:t where t:type)<computes><reads>:t = X
Main():void = Print("{Id(1)}")
