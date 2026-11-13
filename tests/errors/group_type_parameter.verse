# expect: 3:3: a parameter of a parametric type is written t:type or t:subtype(…)
# A parametric type's parameters are types, not a group of them.
box((u:type, v:type)) := class{}
Main():void = {}
