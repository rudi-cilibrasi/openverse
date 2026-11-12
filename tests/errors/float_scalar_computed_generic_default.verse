# expect: effect <reads>
Default(X:t,?V:float=Lerp(0.0,1.0,0.5) where t:type)<computes>:float=V
Pure()<computes>:float=Default(7)
Main():void=Print("{Pure()}")
