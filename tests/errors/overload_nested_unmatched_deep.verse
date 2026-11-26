# expect: 11:155: no overload of Depth takes (int)
# tests/verse/overload_char_string's call of Depth, twenty-four deep, without
# the overload its innermost argument fits (#769, the mutant a nightly fuzz
# run found): refused as the six-deep one is
# (tests/errors/overload_nested_unmatched), where each level asked for its
# argument five times over and this did not end
# (tests/scripts/test-overload-refusal-nests.sh bounds it and its neighbours).
Depth(S:string):int = 0
Depth(C:char):int = 2
Main():void =
    Print("{Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(Depth(1))))))))))))))))))))))))}")
