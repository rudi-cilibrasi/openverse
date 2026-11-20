# Book: Tests/Bugs/FORT-741838-SuccessFailureParametricTypes.versetest 72, 83,
# decls (3 cases): a class's type parameter given as a function's explicit
# type argument, Nothing(t) in holder(t) (the where-introduced variable of
# TypeParam.versetest:49, book-typeparam-as-value, is refused, 9001). The
# Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "t, a type parameter, given
# as Nothing's type argument t: openverse takes the BPVM's reading, a link
# error (Book of Verse tests, TypeParam.versetest:43; VerseVM accepts it,
# :49)"
# If UEFN 43.12 admits it, it prints
#   empty
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Nothing(t:type):?t = false

holder(t:type) := class:
    Empty():?t = Nothing(t)

Main():void =
    H := holder(int){}
    E := H.Empty()
    if (not E?):
        Print("OVPROBE empty")
