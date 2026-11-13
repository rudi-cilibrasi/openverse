# expect: field 'Limit' is <final> in base: child cannot override it
base := class:
    Limit<final>:int = 10
child := class(base):
    Limit<override>:int = 20
Main():void = {}
