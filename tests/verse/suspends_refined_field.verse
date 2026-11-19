# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
# a #157 interface field read in a suspends function (#179)
holder(t:type) := interface:
    var Item:t
base := class:
    X:int = 9
sub(t:type) := class(base, holder(t)):
    Y:int = 1
intbox := class(holder(int)):
    N:int = 0
strbox := class(holder(string)):
    S:string = "s"
Tick(X:t where t:type)<suspends>:t = X
Get(H:holder(t) where t:type)<suspends>:t =
    Sleep(0.1)
    H.Item
Main()<suspends>:void =
    I := intbox{Item := 1}
    Print("{Get(I)}")
