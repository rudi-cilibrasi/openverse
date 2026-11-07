# expect: 6:32: Make constructs an object that has a var field or is <unique>
token := class<unique>:
    N:int = 0
holder := class:
    T:token = token{}
Make()<computes>:holder = holder{}
Main():void = Print("{Make().T.N}")
