# Overloaded functions with several values (#283) called in the entry expression (`do`), whose
# overload is picked as anywhere else
Two(N:int)<transacts>:int = N | N * 10
Two(S:string)<transacts>:int = S.Length | 100
Main():void = {}
