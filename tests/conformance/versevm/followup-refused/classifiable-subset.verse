# Book: Tests/ClassifiableSubset.versetest 11, 19, 30, 41, 52, 165, 169, 173,
# 215, 220, 224, 228, 236, 241, 245, 253, 263, 326, 340, 350 (20 cases, 5 of
# them depends_on_library): a classifiable_subset(t) made by
# MakeClassifiableSubset and asked with Contains (the Book's API reference
# lists MakeClassifiableSubset as experimental, FN 3800+). The Book's tests
# expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown parametric type
# 'classifiable_subset' (only structs can be parametric)"
# If UEFN 43.12 admits it, it prints
#   contains base_type
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
# Control: classifiable-subset-control (the <castable> class and an array of
# it, without the subset).
base_type := class<castable>{}

Main():void =
    C:classifiable_subset(base_type) = MakeClassifiableSubset(array{base_type{}})
    if (C.Contains[base_type]):
        Print("OVPROBE contains base_type")
