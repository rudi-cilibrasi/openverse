left := interface { Go(X:int,?N:int=0)<suspends>:int }
right := interface { Go(X:string,?N:string="")<suspends>:string }
both := class(left,right):
    SeedL:int=3
    SeedR:string="r"
    (left:)Go<override>(X:int,?N:int=block{Print("left default");SeedL})<suspends>:int=block{Sleep(0.02);N}
    (right:)Go<override>(X:string,?N:string=block{Print("right default");SeedR})<suspends>:string=block{Sleep(0.01);N}
Main()<suspends>:void=
    C:=both{}
    L:=spawn{C.(left:)Go(1)}
    R:=spawn{C.(right:)Go("x")}
    Print("created")
    Print("results {L.Await()} {R.Await()}")
