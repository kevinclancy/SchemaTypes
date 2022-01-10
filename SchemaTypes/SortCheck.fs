module SortCheck

open CheckComputation
open Syntax

let rec applyProofs (ctxt : SortContext) (sort : Sort) : Check<Sort> =
    match sort with
    | StFun(varName, StProof(ind,prfRng), cod, rng) ->
        let provesInd (a : string, q : Sort, s : Set<Satellite>, e : EntryType) =
            match q with
            | StProof(j, _) when ind.IndexEquals(j) ->
                true
            | _ ->
                false
        match List.tryFind provesInd ctxt with
        | Some(a, StProof(j, _), _, _) ->
            applyProofs ctxt (cod.subst(IndVar(a,noRange), varName))    
        | Some(_,_,_,_) ->
            failwith "impossible"
        | None ->
            Error [("Proof of " + ind.ToString() + " not in context.", noRange)]
    | _ ->
        Result sort

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
            do! withError "codomain sort ill-formed" rng <| wfSort ((varName, dom, Set.empty, CStandard) :: ctxt) cod
        }

and wfSortContext (ctxt : SortContext) : Check<unit> =
    match ctxt with
    | (var, st, s, _) :: rest ->
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
                    Error [("Expected " + fn.ToString() + " to have a function sort. Instead it has the sort " + fnSort.ToString(), rng)]
            let! applied =
                match argSort.SortEquals(dom) with
                | true ->
                    Result <| cod.subst(arg,varName)
                | false ->
                    Error [("Argument sort " + argSort.ToString() + " does not match domain sort " + dom.ToString(), rng)]
            let! result = applyProofs ctxt applied
            return result
        }
    | IndVar(varName, rng) ->
        match List.tryFind (fun (x,_,_,_) -> x = varName) ctxt with
        | Some(_, sort, _, _) ->
            Result sort
        | None ->
            Error [("Sort variable " + varName + " not in sorting context.", rng)]
    | IndTrue(_) ->
        Result <| StProp(noRange)