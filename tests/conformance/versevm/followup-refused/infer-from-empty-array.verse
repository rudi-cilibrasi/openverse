# Book: Tests/Bugs/SOL-5452-NullDereferenceAfterRuntimeError.versetest:6;
# Tests/Intrinsics/ArrayReplaceAll.versetest:12;
# Tests/Bugs/2023-02-08-MapMemoryLeak.versetest:11 (3 cases): a generic
# function's type parameter given only by an empty array{} (the Book's cases:
# F(array{}, 0), array{}.ReplaceAll(...), map{}.RemoveKey[0]). The Book's
# tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "cannot infer type parameter
# t of Count from the arguments of this call"
# If UEFN 43.12 admits it, it prints
#   count 0
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Count(Items:[]t where t:type):int = Items.Length

Main():void =
    Print("OVPROBE count {Count(array{})}")
