# expect: @perf is not allowed on a function: the attribute class perf has the scopes @attribscope_class
# A custom attribute on a qualified definition of a module is on the
# definition, a function here, which its class's scope does not allow
# (Book of Verse ch. 12, "Attribute Scopes").
M := module:
    @attribscope_class
    perf<public> := class<computes>(attribute){}
    @perf
    (M:)F<public>():int = 1
Main():void = Print("{M.F()}")
