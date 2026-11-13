Drop(T:t where t:subtype(task(int)))<suspends>:void=
    if(T.Cancel(),true?)then ()
Main():void={}
