# A `;` may end a braced block, before its `}` (Book of Verse tests:
# `GetSelf():C= { return(Self); }`, `f():int={1; 2;}`); the block's value is
# its last expression's.
c := class:
    V:int = 4
    GetSelf():c = { return(Self); }
Two():int = {1; 2;}
Main():void =
    if (A := first{Two() = 2; 5;}):
        Print("{c{}.GetSelf().V} {Two()} {A}")
