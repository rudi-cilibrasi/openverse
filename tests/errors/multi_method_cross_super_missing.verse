# expect: nothing above child implements 'Other'
base := class {}
child := class(base):
    Other():int=7
    Values():int=(super:)Other()|9
Main():void=for(V:=child{}.Values()):Print("{V}")
