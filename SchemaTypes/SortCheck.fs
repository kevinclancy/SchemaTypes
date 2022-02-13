module SortCheck

open CheckComputation
open Syntax

let rec applyProofs (ctxt : SortContext) (sort : Sort) (rng : Range) : Check<Sort> =
    match sort with
    | StFun(varName, StProof(ind,_), cod, _) ->
        let provesInd (a : string, q : Sort) =
            match q with
            | StProof(j, _) when ind.IndexEquals(j) ->
                true
            | _ ->
                false
        match List.tryFind provesInd ctxt with
        | Some(a, StProof(j, _)) ->
            applyProofs ctxt (cod.subst(IndVar(a,noRange), varName)) rng  
        | Some(_,_) ->
            failwith "impossible"
        | None ->
            Error [("Proof of " + ind.String + " not in context.", rng)]
    | _ ->
        Result sort

let rec wfSort (ctxt : SortContext) (sort : Sort) : Check<unit> =
    match sort with
    | StString(_)
    | StProp(_)
    | StStringLit(_,_) ->
        Result ()
    | StProof(ind,rng) ->
        check {
            let! indSort = withError (ind.String + " failed to sort check.") rng <| sortCheckInd ctxt ind
            do!
                match indSort with
                | StProp(_) ->
                    Result ()
                | _ ->
                    Error [("Expected " + ind.String + " to have sort prop, but instead it has sort " + indSort.String, rng)]
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
            // todo: check that satellites s are well formed
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
            let! argSort = sortCheckInd ctxt arg
            let! varName,dom,cod =
                match fnSort with
                | StFun(varName, dom, cod, _) ->
                    Result (varName,dom,cod)
                | _ ->
                    Error [("Expected " + fn.String + " to have a function sort. Instead it has the sort " + fnSort.String, rng)]
            let! applied =
                match argSort.SortEquals(dom) with
                | true ->
                    Result <| cod.subst(arg,varName)
                | false ->
                    Error [("Argument sort " + argSort.String + " does not match domain sort " + dom.String, rng)]
            let! result = applyProofs ctxt applied arg.Range
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