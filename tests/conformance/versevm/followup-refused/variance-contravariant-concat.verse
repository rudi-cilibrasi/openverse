# Book: Tests/Bugs/SOL-6739-ParametricTypeMeetAndJoin.versetest 58, 161 (2
# cases): an array of contravariant_class_impl(comparable), a subclass that
# also holds t in a field, appended to an array of contravariant_class(int).
# The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "cannot concatenate
# []contravariant_class(int) and []contravariant_class_impl(comparable):
# contravariant_class_impl(comparable) is a contravariant_class(int) by
# contravariant_class's variance (Book of Verse ch. 10), but not in openverse
# yet: contravariant_class_impl, a class below contravariant_class, holds it
# in its field Data, and Verse Core types a reference by its object's own
# class (docs/research/variance.md)"
# If UEFN 43.12 admits it, it prints
#   method 1
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
contravariant_class(t:type) := class<abstract>:
    Method(X:t):int

contravariant_class_impl(t:subtype(comparable)) := class(contravariant_class(t)):
    Data:t
    Method<override>(X:t):int = 1

Main():void =
    var Xs:[]contravariant_class(int) = array{}
    set Xs += array{contravariant_class_impl(comparable){Data := 2}}
    if (First := Xs[0]):
        Print("OVPROBE method {First.Method(5)}")
