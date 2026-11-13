# expect: <writes> on class/interface is redundant: <transacts> implies it
c := class<transacts><writes> { var X:int = 0 }
Main():void = {}
