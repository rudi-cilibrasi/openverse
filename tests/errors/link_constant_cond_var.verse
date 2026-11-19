# expect: computing the constant Submodule.C0 allocates the var X declared in F
# The var is on the path the initialiser takes (F(true)): a link error on
# Epic's Verse VM (UEFN 43.12, probe book-global-block-cond-var) and in the
# Book's tests (GlobalVariables.versetest:105, verse_vm_only); its control,
# F(false), links (tests/verse/link_constant_controls.verse).
F(Condition:logic)<allocates>:int =
    if (Condition?):
        var X:int = 0
    return 1
c0 := class<allocates>{block{F(true)}}
Submodule := module:
    C0:c0 = c0{}

Main():void =
    Print("linked")
