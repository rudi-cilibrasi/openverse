# Does Sleep(0.0) resume on the next update (the Book's API reference;
# OpenVerse: one tick, as any duration of at most one tick), or can it
# resume in the same update (the Book's prose, ch. 14: "may resume in the
# same tick if no other work is pending")? A sleeps zero three times; B
# sleeps the shortest positive time once, which resumes on the next update
# and never sooner (the API reference).
# OpenVerse prints (B on the first update, A on the third):
#   b after short sleep | a after three zero sleeps | main after wait
# If zero sleeps resume within the update they were made in:
#   a after three zero sleeps | b after short sleep | main after wait
A()<suspends>:void =
    Sleep(0.0)
    Sleep(0.0)
    Sleep(0.0)
    Print("OVPROBE a after three zero sleeps")

B()<suspends>:void =
    Sleep(0.001)
    Print("OVPROBE b after short sleep")

Main()<suspends>:void =
    spawn{A()}
    spawn{B()}
    Sleep(0.5)
    Print("OVPROBE main after wait")
