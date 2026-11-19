# expect: F takes 1 positional argument(s), found 2: several arguments are not packed into a generic parameter beside a named one
# Several arguments are not packed into a generic parameter beside a named
# one either (#724): UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086)
# refuses F(1, 2, ?E := 5) of F(X:t, ?E:int where t:type), error 3509,
# "This function parameter expects a value of type tuple(any,?E:int), but
# this argument is an incompatible value of type
# tuple(type{1},type{2},?E:type{5})" (followup-book4/generic-param-named-pack).
F(X:t, ?E:int where t:type):int = E
Main():void = Print("{F(1, 2, ?E := 5)}")
