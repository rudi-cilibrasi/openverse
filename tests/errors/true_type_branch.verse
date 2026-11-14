# expect: expected tuple(), found any
# A branch's value is no value of the program's (an any): the Book's tests
# take `Result:any = branch: …` and refuse `Result:true = branch: …`
# (Bugs/FORT-582630-BranchResult.versetest 3-14).
Immediate()<suspends>:int = 0
BranchTest()<suspends>:void =
    Result:true = branch:
        Immediate()
Main():void = {}
