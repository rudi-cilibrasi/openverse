# Book:
# Tests/Bugs/SOL-3564-CallingSuperClassMethodFromOverriddenMethod.versetest
# 57, 66, 201, decls; Tests/ShadowDefinition.versetest 113, 128, 145, 146,
# 199; Tests/InterfaceWithFields.versetest 562, decls (11 cases): a class's
# own method (derived:)F beside the F it inherits, two members of one name
# told apart by their qualifiers (ch. 10, "Methods with Same Name"). The
# Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "(derived:)F: a second method
# F beside the one derived inherits (Book of Verse ch. 10, "Methods with Same
# Name"): openverse does not support two methods of one name in a class;
# override the inherited one with F<override>, or give this one another name"
# If UEFN 43.12 admits it, it prints
#   base 1 own 2
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
base := class:
    F():int = 1

derived := class(base):
    (derived:)F():int = 2

Main():void =
    D := derived{}
    Print("OVPROBE base {D.(base:)F()} own {D.(derived:)F()}")
