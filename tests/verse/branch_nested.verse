# a branch inside a branch: each wrapper drives its own arm (#156)
# (#724: a branch and a rush's arm that goes on are children of the task whose
# code started them, stopped when that task ends, after its own defers: Epic's
# Verse VM, UEFN 43.12; no longer when the function that started them exits.)
Outer()<suspends>:void =
    branch:
        branch:
            loop:
                Sleep(1.0)
                Print("inner tick")
        loop:
            Sleep(1.5)
            Print("outer tick")
    Sleep(3.2)
    Print("outer exits")
Main()<suspends>:void =
    Outer()
    Sleep(2.0)
    Print("end")
