# expect: Bump sets a var field, which its effects (<reads>) do not allow
cell(t:type) := class:
    var Value:t
Bump(C:cell(int))<reads>:void = set C.Value += 1
Main():void = Print("x")
