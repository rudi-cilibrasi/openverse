# Overloaded functions with several values (#283) called in the entry expression (`do`), whose
# overload is picked as anywhere else
Two(N:int):int = N | N * 10
Two(S:string):int = S.Length | 100
Main():void = {}
