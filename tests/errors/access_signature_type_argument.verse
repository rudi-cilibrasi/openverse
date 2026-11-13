# expect: Boxed names inner, which is less visible: inner is internal to the top level
# (ParametricTypes.versetest:1260: a parametric type's arguments count, FN36.00)
box<public>(t:type) := class<computes>:
    Has:int = 0
inner := class{}
Boxed<public>:box(inner) = box(inner){}
Main():void = {}
