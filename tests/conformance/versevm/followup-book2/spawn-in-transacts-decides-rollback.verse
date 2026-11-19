# Book: Tests/SoftwareTransactionalMemory.versetest:505 (bp_vm_only), as
# spawn-in-transacts-decides: here the condition fails after the spawn.
# OpenVerse undoes the spawn with the failed condition (the task never
# prints) and prints
#   before sleep | after sleep
# Other readings: the task survives the rollback (spawned undone, before or
# after before sleep; the Verse VM may label a rolled-back line "(Rolling
# Back)"), or a runtime error. Asked only if spawn-in-transacts-decides is
# admitted.
Work(Tag:string)<suspends>:void =
    Print("OVPROBE spawned {Tag}")

SpawnIn(Tag:string)<transacts><decides>:void =
    spawn{Work(Tag)}

Main()<suspends>:void =
    Limit := 0
    if (SpawnIn["undone"], Limit > 0):
        Print("OVPROBE condition succeeded")
    Print("OVPROBE before sleep")
    Sleep(0.0)
    Print("OVPROBE after sleep")
