# expect: calls base.Step, which has the effect <writes>
base := class:
    var N:int = 0
    Step()<transacts>:void = set N += 1
sub := class(base):
    Step<override>()<reads>:void = (super:)Step()
Main():void = sub{}.Step()
