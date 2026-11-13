# expect: tag is a constructor of an attribute class: it is named in attributes only
@attribscope_function
tag_attribute := class<computes>(attribute) {}
tag<constructor>(Text:string)<computes> := tag_attribute{}
F():void =
    X := tag("a")
Main():void = {}
