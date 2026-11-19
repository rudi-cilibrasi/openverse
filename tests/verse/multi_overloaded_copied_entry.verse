# Copied overload selection also retains the entry expression when helpers are added.
Dup(V:t where t:type):t = V | V
Pick(N:int)<transacts>:int = N | N + 1
Pick(S:string)<transacts>:int = 7 | 8
Main():void = {}
