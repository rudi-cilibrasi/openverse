# Module constants that allocate no var link and run (#724): the Book's
# control, whose var is on a path its initialiser does not take
# (GlobalVariables.versetest:143, valid on both VMs; it printed `linked` on
# Epic's Verse VM and Blueprint VM, UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, probe
# book-global-block-cond-var-control), and ordinary constants: computed with
# a for, with a class's block that allocates nothing, with a function that
# declares a var only on a path not taken, beside functions that do declare
# vars and are called from Main (not from a constant).
# Run with --extended-defaults: Limit is defined by a call of a function of
# the program, which Epic's compiler refuses in a data member (3582, UEFN
# 43.12) and openverse refuses too without the flag.
F(Condition:logic)<allocates>:int =
    if (Condition?):
        var X:int = 0
    return 1
c0 := class<allocates>{block{F(false)}}
Submodule := module:
    C0:c0 = c0{}

point := class<computes>:
    X:int
    Y:int
    block:
        Unused := X + Y

Squares:[]int = for (I := 1..4) { I * I }
Origin:point = point{X := 0, Y := 0}
Limit:int = Choose(false)

Choose(Count:logic)<computes>:int =
    if (Count?):
        var N:int = 0
        for (I := 1..3):
            set N += I
        return N
    7

Summed(Upto:int):int =
    var Total:int = 0
    for (I := 1..Upto):
        set Total += I
    Total

Main():void =
    Print("linked")
    Print("squares {Squares.Length}")
    Print("origin {Origin.X} {Origin.Y}")
    Print("limit {Limit}")
    Print("summed {Summed(Limit)}")
