# expect: the module 'Thing' has the name of the module Thing (2:0): Verse does not allow shadowing
Thing := module:
    Thing := module{}
Main():void = {}
