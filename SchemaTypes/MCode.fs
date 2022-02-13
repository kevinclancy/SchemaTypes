module MCode

type MCode =
    | MLine of string
    | MBlock of List<MCode>
    | MBlockVar of int

type MCode with
    member this.subst(var : int, codeToSub : MCode) =
        match this with
        | MLine(x) ->
            MLine(x)
        | MBlock(stats) ->
            MBlock <| List.map (fun (x : MCode) -> x.subst(var, codeToSub)) stats
        | MBlockVar(n) when n = var ->
            codeToSub
        | MBlockVar(n) ->
            MBlockVar(n)

    member this.String =
        let rec toStringAux (depth : int) (code : MCode) =
            match code with
            | MLine(str) ->
                if depth = 0 then
                    str
                else
                    " " + (String.replicate (depth - 1) "  ") + str
            | MBlock(code) ->
                String.concat "\n" (List.map (toStringAux <| depth+1) code)
            | MBlockVar(n) ->
                "(" + n.ToString() + ")"
        toStringAux 0 this