# Book: Tests/SoftwareTransactionalMemory.versetest:505 (bp_vm_only, "STM
# doesn't support spawn, don't allow in decides"): spawn in a
# <transacts><decides> function. The Book's Blueprint VM refuses it, 3512
# twice; there is no Verse VM twin. OpenVerse admits it; the call succeeds
# and the task runs at once:
#   spawned kept | call succeeded | before sleep | after sleep
# If the Verse VM starts the task when the transaction commits: call
# succeeded | spawned kept | ... or later. If UEFN 43.12 refuses it (Build
# Verse Scripts, or the cook of a Verse VM session), Epic's shipped
# toolchain refuses a program OpenVerse runs. The rollback is
# spawn-in-transacts-decides-rollback.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3512 (L15) "This 'spawn' macro has the
# 'no_rollback' effect, which is not allowed by its context."; 3512 (L15)
# "This invocation calls a function (`(<project>:)Work`) that has the
# 'no_rollback' effect, which is not allowed by its context.".
Work(Tag:string)<suspends>:void =
    Print("OVPROBE spawned {Tag}")

SpawnIn(Tag:string)<transacts><decides>:void =
    spawn{Work(Tag)}

Main()<suspends>:void =
    if (SpawnIn["kept"]):
        Print("OVPROBE call succeeded")
    Print("OVPROBE before sleep")
    Sleep(0.0)
    Print("OVPROBE after sleep")
