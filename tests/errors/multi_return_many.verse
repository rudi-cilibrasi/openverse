# expect: 2:0: F has several values and 20 ifs with a return: more than 16
F(X : int)<transacts>:int =
    if (X > 1):
        if (X = 100):
            return 1
        Print("t1")
    if (X > 2):
        if (X = 200):
            return 2
        Print("t2")
    if (X > 3):
        if (X = 300):
            return 3
        Print("t3")
    if (X > 4):
        if (X = 400):
            return 4
        Print("t4")
    if (X > 5):
        if (X = 500):
            return 5
        Print("t5")
    if (X > 6):
        if (X = 600):
            return 6
        Print("t6")
    if (X > 7):
        if (X = 700):
            return 7
        Print("t7")
    if (X > 8):
        if (X = 800):
            return 8
        Print("t8")
    if (X > 9):
        if (X = 900):
            return 9
        Print("t9")
    if (X > 10):
        if (X = 1000):
            return 10
        Print("t10")
    X | X + 1
Main()<transacts>:void =
    for (V := F(3)):
        Print("f {V}")
