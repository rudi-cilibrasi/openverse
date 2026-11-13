# expect: field 'Limit' is <final> in base: a construction of base cannot give it a value
base := class:
    Limit<final>:int = 10
Main():void =
    B := base{Limit := 3}
    Print("{B.Limit}")
