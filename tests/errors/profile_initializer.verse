# expect: profile is not allowed in the default of 'V': an initializer
c := class:
    V:int = profile("v"){1+2}
Main():void = {}
