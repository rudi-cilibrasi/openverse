# A set through a call's result, here a getter's on a choice's values in a
# for, writes the object the call gives: the root first, then the value
# (the Book's tests, AssignmentSequencing.versetest 17-48; refused before,
# "not through a tuple element or a call result").
leaf:=class{var K:int=1}
ca:=class{C:leaf;Get()<computes>:leaf=C}
cb:=class{C:leaf;Get()<computes>:leaf=C}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    L1:=leaf{}
    L2:=leaf{}
    Rows:=for(A:=(Dup(ca{C:=L1})|Dup(cb{C:=L2}))):set A.Get().K+=1
    Print("{Rows.Length} {L1.K} {L2.K}")
    for(R:Rows):Print("{R}")
