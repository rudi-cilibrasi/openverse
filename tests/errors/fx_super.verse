# expect: Look calls base.Step, which has the effect <writes>
base := class:
    var N:int = 0
    Step()<transacts>:void = set N += 1
sub := class(base):
    Step<override>()<transacts>:void = (super:)Step()
    Look()<reads>:void = (super:)Step()
Main():void = sub{}.Look()
