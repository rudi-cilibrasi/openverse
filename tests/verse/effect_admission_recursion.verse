# No termination promise is inferred from <computes> or from execution fuel.
Forever()<computes>:int = Forever()
predicts()<computes>:int = 7
Main():void =
    Print("<converges> and <predicts> are text here")
    Print("{predicts()}")
