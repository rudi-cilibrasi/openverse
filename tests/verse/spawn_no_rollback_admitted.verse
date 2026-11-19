# Where a spawn is admitted (#724): a spawn has the no_rollback effect, so a
# function without a heap specifier may spawn (UEFN 43.12 admits
# followup-book2/spawn-in-transacts-computes-control and runs it on the
# Verse VM: started, after sleep), as may an if's branch, and the top of a
# plain <decides> function's body, as it may call a function without a heap
# specifier there (UEFN 43.12 admits followup/decides-body-default-call;
# StartIf is only compiled: a plain <decides> function, which has
# no_rollback, cannot be called in a condition, followup/decides-plain-if).
Work(Tag:string)<suspends>:void =
    Print("spawned {Tag}")
Start(Tag:string):void = spawn{Work(Tag)}
StartIf(Tag:string, Go:logic)<decides>:void =
    spawn{Work(Tag)}
    Go?
Main()<suspends>:void =
    Start("plain")
    Limit := 1
    if (Limit > 0):
        spawn{Work("branch")}
    Sleep(0.0)
    Print("after sleep")
