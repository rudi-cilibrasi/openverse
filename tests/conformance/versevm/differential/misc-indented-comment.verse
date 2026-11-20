# The extent of an indented comment: the lines after it indented by two
# spaces more are part of it, whatever the amount.
# Tests LANGUAGE.md, Readings, "Extent of a [indented comment marker]
# comment": "everything indented by four spaces on subsequent lines" (the
# Book's prose); openverse (the Book's tests): "the rest of the [marker]
# line and every following line indented more than that line, whatever the
# amount". (The marker is less-than, hash, greater-than; written out it
# would start a comment inside this one.) If only lines indented by four
# spaces were comment, the two-space line below would be code (and
# misindented).
# OpenVerse prints (Lean and C agree):
#   before | after
Main():void =
    Print("OVPROBE before")
    <#>
      Print("OVPROBE commented two")
        Print("OVPROBE commented four")
    Print("OVPROBE after")
