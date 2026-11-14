# expect: starts a task with spawn{…} (which has <transacts>'s effects
# A spawn has <transacts>'s heap effects, besides those of the call it
# starts (the Book's tests, Effects.versetest: "spawn requires the transacts
# effect in addition to the effects of the spawned async function"): a
# <computes> function cannot spawn, also of a <computes> function
Child()<suspends><computes>:void=
    Print("start")
    Sleep(0.01)
    Print("after wait")
Main()<computes>:void=
    T:=spawn{Child()}
