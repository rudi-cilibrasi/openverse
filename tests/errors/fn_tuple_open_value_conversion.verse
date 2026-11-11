# expect: expected type{_(:int, :string):tuple(int, string)}, found type{_(:tuple(int, string)):tuple(int, string)}
Id(X:t where t:type):t=X
Main():void=
    F:type{_(:tuple(int,string)):tuple(int,string)}=Id
    G:type{_(:int,:string):tuple(int,string)}=F
    Print("wrong")
