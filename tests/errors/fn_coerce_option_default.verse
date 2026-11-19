# expect: using a value of type ?type{_(?A:int = …):int} as a value of type ?type{_():int} is not yet implemented
# (#724) option{F2} where a ?type{_():int} is expected: Epic's compiler types
# the option at F2's own type and converts it (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502,
# "Using a value of type ?((?A:int = ...)->int) as a value of type
# ?(tuple()->int)": followup-coerce/option-of-fn-default), where an array's
# and a tuple's elements are named at their types (admitted).
F2(?A:int = 2):int = A
Main():void =
    O:?type{_():int} = option{F2}
    if (F := O?):
        Print("{F()}")
