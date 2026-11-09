# a spawn in a generic function that calls itself at ever bigger option
# types (#244, #249)
F0(X:t, N:int where t:type)<suspends>:int =
    if (N > 0):
        T := spawn{F0(option{X}, N - 1)}
        T.Await()
    else:
        0
Main()<suspends>:void =
    Print("result {F0(1, 1)}")
