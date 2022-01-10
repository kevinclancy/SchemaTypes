module DecisionProcedures

open Syntax

let (|FlatApp|_|) (ind : Index) : Option<string * List<string>> =
    
    let rec (|FlatAppAux|_|) (ind : Index) : Option<string * List<string>> =
        match ind with
        | IndApp(fn, IndVar(arg,_), _) ->
            match fn with
            | FlatAppAux (predName, args) ->
                Some (predName, arg :: args)
            | _ ->
                None
        | IndVar(predName, _) ->
            Some (predName, [])
        | _ ->
            None

    match ind with
    | FlatAppAux (predName, args) ->
        Some (predName, List.rev args)
    | _ ->
        None

let addDecisionProcedure (ctxt : SortContext) (ind : Index) : SortContext =
    match ind with
    | FlatApp(fn, args) ->
        let rec makePath (ctxt : SortContext) (args : List<string>) : List<DecisionProcedureKey> =
            match ctxt with
            | (_, _, _, CStandard) :: rest ->
                makePath rest args
            | (_, StStringLit(s,_), _, CPhysical) :: rest ->
                LiteralKey s :: makePath rest args
            | (varName, StString(_), _, CPhysical) :: rest ->
                match List.tryFindIndex (fun x -> x = varName) args with
                | Some n ->
                    ArgumentKey n :: makePath rest args
                | None ->
                    WildcardKey :: makePath rest args
            | _ ->
                failwith "unreachable"

        let indDependsOnEntry (varName : string, sort : Sort, satellites : Set<Satellite>, entryType : EntryType) =
            varName = fn || (not <| Set.isEmpty (Set.intersect sort.freeVars (Set.ofSeq (List.toSeq args))))

        let rec add (ctxt : SortContext) : SortContext =
            match ctxt with
            | (varName, sort, satellites, entryType) as first :: rest ->
                match indDependsOnEntry (varName, sort, satellites, entryType) with
                | true ->
                    (varName, sort, satellites.Add <| DecisionProcedure (fn, makePath ctxt args), entryType) :: rest
                | false ->
                    first :: add rest
            | [] ->
                failwith "unreachable if the index is well sorted in the context"

        add ctxt
    | _ ->
        ctxt