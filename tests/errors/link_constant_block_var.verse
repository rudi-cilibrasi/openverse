# expect: computing the constant C0 allocates the var X declared in the block of c0: Epic's Verse VM computes a module's constants when it links the program
# A module constant whose computation allocates a var: Epic's Verse VM fails
# the link (Script error 9003, "Runtime error while evaluating module.", UEFN
# 43.12, ++Fortnite+Release-43.12-CL-60598086, probe book-global-block-var),
# as the Book's tests expect (GlobalVariables.versetest:86, verse_vm_only).
# Here the class's block declares the var.
c0 := class<allocates>{block{var X:int = 0}}
C0:c0 = c0{}

Main():void =
    Print("linked")
