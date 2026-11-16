RunTrue(X:t where t:type):int=
    R:=for(A:=if(1=1)then(X|X)else X){A}
    R.Length
RunFalse(X:t where t:type):int=
    R:=for(A:=if(1=0)then(X|X)else X){A}
    R.Length
RunEmpty(X:t where t:type):int=
    R:=for(A:=array{X}[1]){A}
    R.Length
Main():void=
    Print("{RunTrue(1)}")
    Print("{RunFalse(1)}")
    Print("{RunEmpty(1)}")
    Print("{RunFalse(1)}")
