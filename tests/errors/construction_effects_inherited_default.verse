# expect: default of field 'Value' of parent
source:=class<reads>{}
parent(t:type):=interface<computes>:
    Value:source=source{}
child:=class<computes>(parent(int)){}
Main():void={}
