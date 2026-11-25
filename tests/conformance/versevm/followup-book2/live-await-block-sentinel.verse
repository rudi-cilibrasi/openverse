# Sentinel for the live-variables cause: Book: Tests/await.versetest:6
# (verse_vm_only, valid): await{1}, the await expression of ch. 15 (not an
# event's Await()). UEFN 43.12 refuses live (book-live-set, 3506); is
# await{...} known? Kept in a function that is not called, so a run cannot
# wait on it. OpenVerse refuses it (unknown struct 'await'). If UEFN admits
# it, OpenVerse prints
#   admitted
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3506 (L8) "Unknown identifier `await`.".
Unused()<suspends>:void =
    await{1}

Main():void =
    Print("OVPROBE admitted")
