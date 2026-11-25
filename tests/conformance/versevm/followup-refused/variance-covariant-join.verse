# Book: Tests/Bugs/SOL-6739-ParametricTypeMeetAndJoin.versetest 38, 74, 138,
# 177 (4 cases): the branches of an if, covariant_class(int) and
# covariant_class(any), where a covariant_class(any) is expected (the Book's
# cases also join contravariant ones; OpenVerse admits the join of
# covariant_class(dog) and covariant_class(animal), so its refusal is of an
# int held as an any). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "the branches have different
# types: covariant_class(int) and covariant_class(any): covariant_class is
# covariant in t: t is used in Data (covariant); an int is an any, but not as
# it is: an any holds no value in openverse, which a covariant_class holding
# it cannot be, so covariant_class(int) is no covariant_class(any) in
# openverse (Book of Verse ch. 10, "Covariant")"
# If UEFN 43.12 admits it, it prints
#   joined
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
covariant_class(t:type) := class:
    Data:t

Choose(Flag:logic):covariant_class(any) =
    X := covariant_class(int){Data := 1}
    Y := covariant_class(any){Data := 2}
    if (Flag?) then X else Y

Main():void =
    Z := Choose(true)
    Print("OVPROBE joined")
