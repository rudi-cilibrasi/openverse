# expect: tag_attribute is an attribute class: it is named in attributes only
@attribscope_function
tag_attribute := class<computes>(attribute) {}
F():void =
    X := tag_attribute{}
Main():void = {}
