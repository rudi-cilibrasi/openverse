# expect: :9:11: Make calls c.SetX, which has the effect <writes>, which its effects (<computes>) do not allow
# (a refusal inside the setter call a construction makes: at the field's value)
c := class:
    var X<getter(GetX)><setter(SetX)>:int = external{}
    var D:int = 0
    GetX(:accessor)<transacts>:int = D
    SetX(:accessor, V:int)<transacts>:void = set D = V
Make()<computes>:c =
    c{X := 3}
Main():void = {}
