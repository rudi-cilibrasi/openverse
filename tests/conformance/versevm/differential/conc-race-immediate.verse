# A race whose first arm finishes without suspending: does the second arm
# begin at all?
# Tests LANGUAGE.md, readings audit, "The scheduler rows": "the later arms of
# a race resolved in its first pass already never began" (the Book's tested
# ch. 14 example, 14_concurrency.md:418-421). If every arm begins before the
# race is decided, "arm two begins" is printed too, before the result.
# Arm one is a call of a <suspends> function that returns without
# suspending (an arm must be able to suspend, Concurrency.versetest).
# OpenVerse prints (Lean and C agree):
#   arm one | result 1 | after wait
Instant()<suspends>:int =
    Print("OVPROBE arm one")
    1

Later()<suspends>:int =
    Print("OVPROBE arm two begins")
    Sleep(0.0)
    2

Main()<suspends>:void =
    R := race:
        Instant()
        Later()
    Print("OVPROBE result {R}")
    Sleep(0.1)
    Print("OVPROBE after wait")
