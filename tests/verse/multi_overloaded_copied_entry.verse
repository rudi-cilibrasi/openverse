# Copied overload selection also retains the entry expression when helpers are added.
Dup(V:t where t:type):t = V | V
Pick(N:int):int = N | N + 1
Pick(S:string):int = 7 | 8
Main():void = {}
