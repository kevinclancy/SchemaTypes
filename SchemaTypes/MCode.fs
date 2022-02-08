module MCode

type MCode =
    | MLine of string
    | MBlock of List<MCode>

type MCode with
    member this.String =
        let rec toStringAux (depth : int) (code : MCode) =
            match code with
            | MLine(str) ->
                if depth = 0 then
                    str
                else
                    " " + (String.replicate (depth - 1) ". ") + str
            | MBlock(code) ->
                String.concat "\n" (List.map (toStringAux <| depth+1) code)
        toStringAux 0 this