# Active cancellation must drain children registered after the owner returned.
# Expected independently by both scheduler models in test-scheduler-model.py.
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
                    Sleep(1.0)
                    Print("{Tag} wrong child {N}")
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
