# expect: an array index must be an int
# An opened argument is not an int merely because it is used as an index.
base(t:type):=class{Value:t}
pair(t:type,u:type):=class(base(t)){Other:u}
Bad(B:base(int))<decides>:int=
    var A:[]int=array{0}
    set A[pair[B].Other]=7
    0
Main():void={}
