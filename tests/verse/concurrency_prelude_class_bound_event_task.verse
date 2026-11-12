holder(event:type):=class{V:event}
Main():void=
    T:?task(int)=false
    H:=holder(int){V:=7}
    Print("{H.V}")
