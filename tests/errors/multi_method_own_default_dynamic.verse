# expect: cannot infer the type parameters of Pick
root := class:
    Pick(?X:t=7 where t:type)<transacts>:t=X|X
child := class(root):
    Pick<override>(?X:u="s" where u:type)<transacts>:u=X|X
Main():void =
    R:root=child{}
    for(V:=R.Pick()): Print("{V}")
