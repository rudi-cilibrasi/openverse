# expect: expected type{_(?Factor:float, ?Value:float):float}, found type{_(?Amount:float, ?Rate:float):float}
# Function types preserve named parameter names (Book of Verse ch. 6, #503)
Calculate(?Amount:float, ?Rate:float):float = Amount * Rate
Main():void =
    F:type{_(?Value:float, ?Factor:float):float} = Calculate
    Print("{F(?Value := 2.0, ?Factor := 3.0)}")
