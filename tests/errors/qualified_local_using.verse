# expect: using{(local:)M}: (local:) qualifies a function's locals, and a using names a module
M<public> := module {}
N := module:
    using{(local:)M}
Main():void = {}
