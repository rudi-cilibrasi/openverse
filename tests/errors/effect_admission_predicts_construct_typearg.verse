# expect: <predicts>
holder(t:type):=class{Value:t}
Good()<computes>:int=1
Main():void=
    H:=holder(type{_()<predicts>:int}){Value:=Good}
