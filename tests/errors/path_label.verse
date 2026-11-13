# expect: 4:15: expected a label after '@' in a path
# The label after '@' starts with a letter or digit, as the first one does.
Main():void =
    R := /user@-host
