# expect: Step<override> in fast overrides what fast cannot use: Step of slow is <private>
# (AccessLevelInheritance.versetest:751: error 3593)
slow := class:
    Step<private>():int = 1
fast := class(slow):
    Step<override>():int = 2
Main():void = {}
