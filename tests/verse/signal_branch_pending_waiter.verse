# An owner returns inside its branch's Signal. The running signaler can
# finish its step; the same round must skip another arm of that stopped branch.
Owner(E:event(int), Pending:logic, KeepOwner:logic, Tag:string)<suspends>:void =
    branch:
        defer: Print("{Tag} branch unwinds")
        sync:
            block:
                Sleep(0.1)
                if (Pending?):
                    E.Await()
                    Print("{Tag} waiter resumed")
                else:
                    Print("{Tag} first arm ended")
            block:
                Sleep(0.2)
                E.Signal(1)
                Print("{Tag} signaler continues")
        Print("{Tag} sync complete")
    E.Await()
    Print("{Tag} owner woke")
    if (KeepOwner?):
        Sleep(0.1)
        Print("{Tag} owner ends")

Main()<suspends>:void =
    spawn{Owner(event(int){}, true, false, "cancel")}
    Sleep(0.5)
    spawn{Owner(event(int){}, true, true, "live")}
    Sleep(0.5)
    spawn{Owner(event(int){}, false, false, "complete")}
    Sleep(0.5)
    Print("main ends")
