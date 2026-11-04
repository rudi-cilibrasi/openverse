# The first program.
using { /Verse.org/Simulation }

Fib(N:int):int =
    if (N <= 1) then N else Fib(N - 1) + Fib(N - 2)

Greeting:string = "Hello"

Main():void =
    Print("{Greeting}, Verse!")
    Print("Fib(20) = {Fib(20)}")
