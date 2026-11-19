# 3582 follow-up (#724), compile only: a module constant defined by an
# archetype of a struct without specifiers (no call). OpenVerse refuses it
# before the rule is reached: a struct without specifiers constructs with
# the transacts effect (#512), so "the value of the constant Both constructs
# pair …, which has the effect <writes>", the reading UEFN 43.12 gave a
# class (3512, div-const-constructor). If Epic admits it, the run prints
# "sum 3".
pair := struct:
    A:int = 1
    B:int = 2

Both:pair = pair{}

Main():void =
    Print("OVPROBE sum {Both.A + Both.B}")
