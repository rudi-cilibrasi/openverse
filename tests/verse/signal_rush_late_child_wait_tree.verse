# Active cancellation must drain children registered after the owner returned.
# Expected independently by both scheduler models in test-scheduler-model.py.
# (#724: a branch and a rush's arm that goes on are children of the task whose
# code started them, stopped when it ends, after its defers, or is cancelled,
# before them (Epic's Verse VM, UEFN 43.12); not when their function exits.)
Owner(X:t,Y:t,Tag:string,N:int where t:type)<suspends>:t=
    defer:
        Print("{Tag} owner cleanup {N}")
    E := event(t){}
    branch:
        R := rush:
            block:
                defer:
                    Print("{Tag} active cleanup {N}")
                Sleep(0.1)
                E.Signal(X)
                Print("{Tag} after signal {N}")
                branch:
                    defer:
                        Print("{Tag} late cleanup {N}")
                    branch:
                        defer:
                            Print("{Tag} grandchild cleanup {N}")
                        Sleep(1.0)
                        Print("{Tag} wrong grandchild {N}")
                    Sleep(1.0)
                    Print("{Tag} wrong child {N}")
                branch:
                    defer:
                        Print("{Tag} sibling cleanup {N}")
                    Sleep(1.0)
                    Print("{Tag} wrong sibling {N}")
                Sleep(1.0)
                Print("{Tag} wrong active {N}")
                X
            block:
                defer:
                    Print("{Tag} other cleanup {N}")
                Sleep(1.0)
                Print("{Tag} wrong other {N}")
                X
        Print("{Tag} after rush {N}")
    V := E.Await()
    Print("{Tag} owner done {N}")
    X
Main()<suspends>:void=
    Owner(1,1,"probe",0)
    Print("main continued")
    Sleep(1.0)
    Print("main done")
