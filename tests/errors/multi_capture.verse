# expect: 3:0: F has several values and uses K, which is also the name of a parameter, local, field or method
K:int = 5
F():int = K | K + 1
H(K:int):int = if (V := F()) then V else 0
Main():void = Print("{H(100)}")
