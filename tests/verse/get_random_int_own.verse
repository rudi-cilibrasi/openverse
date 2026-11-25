# GetRandomInt is a soft built-in (#724): a program's own function of the
# name is the one it calls, and it gets no helper.
GetRandomInt(Low:int, High:int):int = Low + High
Main():void = Print("{GetRandomInt(1, 6)}")
