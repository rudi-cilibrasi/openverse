# expect: 4:24: F has several values and uses K, which is also the name of a local here
K:int = 5
F():int = K | K + 1
H(K:int):int = if (V := F()) then V else 0
Main():void = Print("{H(100)}")
