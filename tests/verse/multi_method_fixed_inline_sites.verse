shape(t:type) := class:
    K:int
    Sizes():int = K | K + 1
big := class(shape(int)):
    Sizes<override>():int = 1000
H(O:shape(int)):int = O.Sizes()
Main():void = if (V := H(shape(int){K:=1}) + H(shape(int){K:=1}), V > 3) { Print("{V}") }
