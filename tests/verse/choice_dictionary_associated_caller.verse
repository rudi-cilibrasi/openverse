# Method-local result families retain the caller's type witnesses and aliases.
Dup(X:t where t:type)<computes>:t=X|X
Keep(X:t where t:type)<computes>:t=X
foo(t:type):=class<computes>{V:t}
bar(t:type):=class<computes>{V:t}
ca(t:type):=class:
    Stored:t
    M(X:u where u:type)<computes>:foo(tuple(t,u))=foo(tuple(t,u)){V:=(Stored,X)}
cb(t:type):=class:
    Stored:t
    M(X:u where u:type)<computes>:bar(tuple(t,u))=bar(tuple(t,u)){V:=(Stored,X)}
Use(X:t,Y:u where t:type,u:type):int=
    Rows:=for(A:=(Dup(ca(t){Stored:=X})|Dup(cb(t){Stored:=X})),I:=(1|2)):
        Alias:=A
        B:=Alias.M(Y)
        Saved:=B
        Keep(array{Saved.V}).Length
    Rows.Length
Main():void=
    Print("{Use(7,"value")}")
    Print("{Use("value",array{7})}")
    Print("{Use(array{7},option{"value"})}")
