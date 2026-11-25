# Sentinel for the live-variables cause: Book: Tests/upon.versetest:7
# (verse_vm_only, valid): upon(1){2} (ch. 15). UEFN 43.12 refuses live
# (book-live-set, 3506); is upon known? Kept in a function that is not
# called. OpenVerse refuses it (a parse error). If UEFN admits it, OpenVerse
# prints
#   admitted
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3506 (L7) "Unknown identifier `upon`.".
Unused():void =
    upon(1){2}

Main():void =
    Print("OVPROBE admitted")
