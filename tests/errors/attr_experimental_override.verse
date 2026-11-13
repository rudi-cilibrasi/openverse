# expect: @experimental is not allowed on an override
base := class:
    M():void = {}
derived := class(base):
    @experimental
    M<override>():void = {}
Main():void = {}
