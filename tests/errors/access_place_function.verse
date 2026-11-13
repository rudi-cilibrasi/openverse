# expect: <protected> is not allowed on a module's function
# (ModuleDefinitions.versetest:129: <protected> and <private> are for a class's members)
Tools := module:
    Twice<protected>(X:int):int = 2 * X
Main():void = {}
