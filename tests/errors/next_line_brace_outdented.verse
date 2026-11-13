# expect: 5:0: expected an indented function body
# A braced body's '{' may start the next line at the definition's column, not before it.
M := module:
    F<public>():int =
{
    1
}
Main():void = Print("{M.F()}")
