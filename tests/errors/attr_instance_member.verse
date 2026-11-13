# expect: unknown identifier 'Y'
@attribscope_data
key := class<computes>(attribute):
    V<public>:int
c := class:
    @key{V := Y}
    X:int = 0
    Y:int = 4711
Main():void = {}
