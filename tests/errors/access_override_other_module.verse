# expect: Speed<override> in Fast.car overrides what Fast.car cannot use: Speed of Slow.vehicle is internal to Slow
# (AccessLevelInheritance.versetest:67: an internal field of another module's class)
Slow := module:
    vehicle<public> := class:
        Speed:int = 1
Fast := module:
    car<public> := class(Slow.vehicle):
        Speed<override>:int = 9
Main():void = {}
