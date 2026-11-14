# expect: :9:5: Peek calls c.GetX, which has the effect <writes>, which its effects (<computes>) do not allow
# (a refusal inside the getter call a read of the field is: at the field)
c := class:
    var X<getter(GetX)><setter(SetX)>:int = external{}
    var D:int = 0
    GetX(:accessor)<transacts>:int = D
    SetX(:accessor, V:int)<transacts>:void = set D = V
Peek(O:c)<computes>:int =
    O.X
Main():void = {}
