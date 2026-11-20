# Book: Tests/ClassifiableSubset.versetest 147, 178, 189, 275, 295, 333, 361
# (7 cases): a classifiable_subset_var(t) made by MakeClassifiableSubsetVar,
# added to and removed from (the Book's API reference marks
# MakeClassifiableSubsetVar, Add and Remove <epic_internal>). The Book's tests
# expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown parametric type
# 'classifiable_subset_var' (only structs can be parametric)"
# If UEFN 43.12 admits it, it prints
#   removed
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
base_type := class<castable>{}

Main():void =
    C:classifiable_subset_var(base_type) = MakeClassifiableSubsetVar()
    Key := C.Add(base_type{})
    if (C.Remove[Key]):
        Print("OVPROBE removed")
