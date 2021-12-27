module SortCheck

open CheckComputation
open Syntax

let rec wfSort (ctxt : SortContext) (sort : Sort) : Check<unit> =
    match sort with
    | StString(_) ->
        Result ()
    | StProp(_) ->
        Result ()
    | StProof(ind,rng) ->
        check {
            let! indSort = withError (ind.ToString() + " failed to sort check.") rng <| sortCheckInd ctxt ind
            do!
                match indSort with
                | StProp(_) ->
                    Result ()
                | _ ->
                    Error [("Expected " + ind.ToString() + " to have sort prop, but instead it has sort " + indSort.ToString(), rng)]
        }
    | StFun(varName, dom, cod, rng) ->
        check {
            do! withError "domain sort ill-formed" rng <| wfSort ctxt dom
            do! withError "codomain sort ill-formed" rng <| wfSort ((varName, dom) :: ctxt) cod
        }

and wfSortContext (ctxt : SortContext) : Check<unit> =
    match ctxt with
    | (var, st) :: rest ->
        check {
            do! wfSort rest st
            do! wfSortContext rest
        }
    | [] ->
        Result ()

and sortCheckInd (ctxt : SortContext) (index : Index) : Check<Sort> =
    match index with
    | IndStringLit(str, _) ->
        Result (StString(noRange))
    | IndApp(fn,arg,rng) ->
        check {
            let! fnSort = sortCheckInd ctxt fn
            let! argSort = sortCheckInd ctxt fn
            let! varName,dom,cod =
                match fnSort with
                | StFun(varName, dom, cod, _) ->
                    Result (varName,dom,cod)
                | _ ->
                    Error [("Expected " + fn.ToString() + " to have a function sort. Instead it has the sort " + fnSort.ToString(), rng)]
            let! result =
                match argSort.SortEquals(dom) with
                | true ->
                    Result <| cod.subst(arg,varName)
                | false ->
                    Error [("Argument sort " + argSort.ToString() + " does not match domain sort " + dom.ToString(), rng)]
            return result
        }
    | IndVar(varName, rng) ->
        match List.tryFind (fun (x,_) -> x = varName) ctxt with
        | Some(_, sort) ->
            Result sort
        | None ->
            Error [("Sort variable " + varName + " not in sorting context.", rng)]
    | IndTrue(_) ->
        Result <| StProp(noRange)