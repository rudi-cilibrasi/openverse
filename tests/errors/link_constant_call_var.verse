# expect: computing the constant Submodule.C0 allocates an object of class c1, which has a var field, made in F
# A module constant whose computation constructs an object of a class with a
# var field, through a function its class's block calls: a link error on
# Epic's Verse VM (UEFN 43.12, probe book-global-block-call-var) and in the
# Book's tests (GlobalVariables.versetest:90, verse_vm_only).
F()<allocates>:c1 = c1{}
c0 := class<allocates>{block{F()}}
c1 := class<allocates>{var X:int = 0}
Submodule := module:
    C0:c0 = c0{}

Main():void =
    Print("linked")
