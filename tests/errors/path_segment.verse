# expect: 4:19: a path's segments after its label are identifiers
# After the label, each segment of a path is an identifier: '1b' is not one.
Main():void =
    R := /Verse.org/1b
