# Sentinel for the survey's live-variables cause (57 Verse VM cases): Book:
# Tests/when.versetest:7 (verse_vm_only, valid): when(1){2}, live variables'
# when (the Book's ch. 15, an unreleased feature). UEFN 43.12 refuses live
# (book-live-set, 3506); is when known? Kept in a function that is not
# called, so a run cannot wait on it. OpenVerse refuses it (a parse error).
# If UEFN admits it, OpenVerse prints
#   admitted
Unused():void =
    when(1){2}

Main():void =
    Print("OVPROBE admitted")
