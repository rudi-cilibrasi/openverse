# expect: Size of Shapes.shape cannot be used here: Shapes.shape is internal to Shapes
# (SOL-5564: a member an internal interface introduces, called through a public class)
Shapes := module:
    shape := interface:
        Size<public>():int
    square<public> := class(shape):
        Size<override>():int = 4
    Make<public>():square = square{}
Main():void = Print("{Shapes.Make().Size()}")
