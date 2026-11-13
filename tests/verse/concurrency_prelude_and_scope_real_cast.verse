# A local named like a prelude type, defined in an and, which sees it on its
# right (Book of Verse ch. 7), while the right of the or around it casts to
# the real type: the prelude is loaded for that cast (#521)
Inc(X:int)<decides>:int=X+1
Probe(E:event(int)):int=
    if(((subscribable_event:=Inc) and subscribable_event[5] > 9) or subscribable_event[E]) then 1 else 0
Main():void=Print("{Probe(event(int){})}")
