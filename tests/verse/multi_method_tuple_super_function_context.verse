# Tuple calls preserve instantiated parameter types and call boundaries (#448).
Id(N:int):int = N
base(t:type) := class:
    Count(F:type{_(:t):t},Y:?t):int = 0 | 1
mid(u:type) := class(base(u)):
    Count<override>(F:type{_(:u):u},Y:?u):int = (super:)Count((F,false))
Main():void = for(N:=mid(int){}.Count(Id,false)){Print("{N}")}