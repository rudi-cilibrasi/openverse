# expect: a constant cannot have the effect specifier <computes>
Fresh()<reads>:int = 7
K<computes>:int = Fresh()
Main():void = Print("{K}")
