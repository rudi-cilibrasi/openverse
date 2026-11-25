# expect: computing the constant Submodule.C0 allocates the var X declared in F
# A module constant whose computation allocates a var local of a function its
# class's block calls: a link error on Epic's Verse VM (UEFN 43.12, probe
# book-global-block-fn-var) and in the Book's tests
# (GlobalVariables.versetest:97, verse_vm_only).
F()<allocates>:int =
    var X:int = 0
    return 1
c0 := class<allocates>{block{F()}}
Submodule := module:
    C0:c0 = c0{}

Main():void =
    Print("linked")
