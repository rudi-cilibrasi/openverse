# Book: Tests/Bugs/SOL-3731-CoercionOfParametricFieldOverrides.versetest 22,
# 23, decls (3 cases): an override in a parametric class,
# t:subtype(comparable), whose result is t where the overridden method returns
# comparable. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "sub_class.Method must have
# the signature of super_class.Method, which it overrides"
# If UEFN 43.12 admits it, it prints
#   method gives 3
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
# Control: override-parametric-result-control (the override at the overridden
# signature, comparable).
super_class := class<abstract>:
    Method():comparable

sub_class(t:subtype(comparable)) := class(super_class):
    Field:t
    Method<override>():t = Field

Main():void =
    X:super_class = sub_class(int){Field := 3}
    V := X.Method()
    if (V = 3):
        Print("OVPROBE method gives 3")
