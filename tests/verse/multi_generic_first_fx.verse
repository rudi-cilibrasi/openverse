# a generic generator with effects where the first success is taken: its function of its own at the type the call gives (#235, #246)
Walk(A:[]t, I:int where t:type)<transacts><decides>:t =
    Print("at {I}")
    I < A.Length
    A[I] | Walk[A, I + 1]
Main():void =
    if (S := Walk[array{"a", "bb", "ccc"}, 0], S.Length > 1) then Print(S)
