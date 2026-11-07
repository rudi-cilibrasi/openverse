# Programs of several files (#27): using{"relative_path"} imports a file or a
# directory, relative to the importing file.
using{"modules/shapes"}
using{"modules/assets"}

Main():void =
    Print("area {Area(square{Side := 3})}")
    Print(Hello)
    Print("answer {Answer}, {Data.Length} bytes, first {Data[0] or -1}")
    Print(Helper(5))
