# ReplaceAll with an empty pattern (run alone, last: an implementation that
# loops on the empty match would never return).
# Tests LANGUAGE.md, Array methods: "A.ReplaceAll(Pattern, Replacement)
# (contiguous subarrays, left to right, not overlapping; an empty pattern
# changes nothing)" (an openverse choice; Epic's digest says nothing of an
# empty pattern). Another reading inserts the replacement between every
# element: x-a-b-c-x or -a-b-c-.
# OpenVerse prints (Lean and C agree):
#   before | result [abc] 3
Main()<suspends>:void =
    Print("OVPROBE before")
    Sleep(0.0)
    S := "abc".ReplaceAll("", "-")
    Print("OVPROBE result [{S}] {S.Length}")
