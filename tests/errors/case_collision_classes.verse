# expect: 9:0: the types cc and CC have names that differ only in case
# Two classes of one scope whose names differ only in case (#724): Epic's
# toolchain makes them one type. UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086)
# refuses the second, error 9002, "Found existing type 'CC' that is already
# being created this compile. Please rename the class to be case insensitive
# unique" (followup-book3/case-collision-classes).
cc := class:
    V:int = 1
CC := class:
    V:int = 2
Main():void = Print("{cc{}.V} {CC{}.V}")
