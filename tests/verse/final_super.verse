# <final_super> and the queries of the API reference (Book of Verse ch. 10,
# "Final"; ch. 11, "final_super and Type Queries"):
# GetCastableFinalSuperClass[B, X] gives the castable <final_super> class
# right below B that X's class is or is below; ...FromType[B, T] the same
# for the class a type value T holds; both fail when there is none.
#
#            base<castable>                 tagged (interface)
#             /        \                      |
#    anchor<final_super>  plain        tag_anchor<final_super>(base, tagged)
#            |              |                 |
#          leaf     plain_anchor<final_super>  tag_leaf<final_super>(tag_anchor, tagged)
base := class<castable>:
    Id:int = 0
anchor := class<final_super>(base):
    Kind:string = "anchor"
leaf := class(anchor):
    Extra:int = 1
plain := class(base) {}
plain_anchor := class<final_super>(plain) {}
tagged := interface {}
tag_anchor := class<final_super>(base, tagged) {}
tag_leaf := class<final_super>(tag_anchor, tagged) {}
# not castable: no class or interface above it is <castable>
loose := class {}
loose_anchor := class<final_super>(loose) {}
# a <final_super_base> class's classes right below it are <final_super>
component := class<castable><final_super_base> {}
physics := class<final_super>(component) {}
rigid := class(physics) {}

Name(T:castable_subtype(base), X:base)<computes><decides>:string =
    if (anchor[X], T[X]) then "anchor"
    else if (plain_anchor[X], T[X]) then "plain_anchor"
    else if (tag_anchor[X], T[X]) then "tag_anchor"
    else ""

Query(X:base)<reads>:string =
    if (T := GetCastableFinalSuperClass[base, X], N := Name[T, X]) then N else "none"

QueryType(T:subtype(base))<reads>:string =
    if (GetCastableFinalSuperClassFromType[base, T]) then "found" else "none"

Main():void =
    Print("{Query(anchor{})} {Query(leaf{})} {Query(base{})} {Query(plain{})} {Query(plain_anchor{})} {Query(tag_leaf{})}")
    # below plain, plain_anchor is found
    Print(if (GetCastableFinalSuperClass[plain, plain_anchor{}]) then "plain: found" else "plain: none")
    # below the interface tagged, tag_anchor and tag_leaf list it: the
    # topmost, which a tag_anchor is
    if (T := GetCastableFinalSuperClass[tagged, tag_leaf{}]):
        Print(if (T[tag_anchor{}]) then "tagged: tag_anchor" else "tagged: tag_leaf")
    # the class found is a castable_subtype of B, and casts to it
    if (T := GetCastableFinalSuperClass[base, leaf{Id := 7}], A := T[leaf{Id := 7}]):
        Print("cast: {A.Id}")
    # not castable, not right below, the class itself, a type no class is below
    Print(if (GetCastableFinalSuperClass[loose, loose_anchor{}]) then "loose: found" else "loose: none")
    Print(if (GetCastableFinalSuperClass[anchor, leaf{}]) then "anchor: found" else "anchor: none")
    Print(if (GetCastableFinalSuperClass[int, 42]) then "int: found" else "int: none")
    Print(if (GetCastableFinalSuperClass[any, leaf{}]) then "any: found" else "any: none")
    Print(if (GetCastableFinalSuperClass[component, rigid{}]) then "component: found" else "component: none")
    # from a type: written, held by a value, or not below B at all
    Kind:subtype(base) = leaf
    Print("{QueryType(leaf)} {QueryType(Kind)} {QueryType(plain)} {QueryType(base)}")
    Print(if (GetCastableFinalSuperClassFromType[anchor, base]) then "up: found" else "up: none")
    Print(if (GetCastableFinalSuperClassFromType[base, int]) then "int: found" else "int: none")
    Print(if (GetCastableFinalSuperClassFromType[base, any]) then "any: found" else "any: none")
    Print(if (GetCastableFinalSuperClassFromType[base, tagged]) then "tagged: found" else "tagged: none")
