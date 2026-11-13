# expect: 4:9: the float literal 1.23f32 is not supported
# The Book's tests call f16 and f32 valid syntax, currently unsupported.
F():float =
    X := 1.23f32
    X
Main():void = {}
