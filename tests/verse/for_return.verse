# return from inside a for body (#85): a body that always returns has no type
# of its own; Core's checker types the for at []void

First(A:[]int, D:int):int =
    for (E : A):
        return E
    D

FirstG(A:[]t, D:t where t:type):t =
    for (E : A):
        return E
    D

FindAbove(A:[]int, N:int):int =
    for (X : A, X > N):
        return X
    -1

Find(M:[string]int, K:string):int =
    for (Key -> V : M):
        if (Key = K):
            return V
    0

Main():void =
    Print("{First(array{4, 5}, 0)} {First(array{}, 7)}")
    Print("{FirstG(array{"a", "b"}, "z")} {FirstG(array{}, 9)}")
    Print("{FindAbove(array{1, 5, 9}, 4)} {FindAbove(array{1}, 4)}")
    Print("{Find(map{"a" => 1, "b" => 2}, "b")} {Find(map{}, "q")}")
