# spawn in a condition of a <suspends> function: started in place (not a
# suspension point); undone with the condition when it fails
Worker(N:int)<suspends>:void =
    Print("worker {N} starts")
    Sleep(1.0)
    Print("worker {N} ends")
Main()<suspends>:void =
    if (spawn{Worker(1)}, false?):
        Print("kept 1")
    else:
        Print("undone 1")
    if (spawn{Worker(2)}, true?):
        Print("kept 2")
    Sleep(2.0)
    Print("main ends")
