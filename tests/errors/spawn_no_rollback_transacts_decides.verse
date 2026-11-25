# expect: 9:4: this spawn has the 'no_rollback' effect, which a body whose effects exclude it does not allow
# A <transacts><decides> function cannot spawn either (#724). UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses it with error 3512
# (followup-book2/spawn-in-transacts-decides; the Book's Blueprint VM test
# SoftwareTransactionalMemory.versetest:505).
Work(Tag:string)<suspends>:void =
    Print("spawned {Tag}")
SpawnIn(Tag:string)<transacts><decides>:void =
    spawn{Work(Tag)}
Main()<suspends>:void =
    if (SpawnIn["kept"]) then Print("call succeeded")
