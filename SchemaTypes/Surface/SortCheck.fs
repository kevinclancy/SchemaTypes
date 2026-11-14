module Surface.SortCheck

open CheckComputation
open Surface.Syntax

let lookup (ctxt : SortContext) (varName : string) : Option<Sort> =
    Option.map snd <| List.tryFind (fun (x,_) -> x = varName) ctxt

/// Does ctxt contain a proof of formula?
let proves (ctxt : SortContext) (formula : Formula) : bool =
    match formula with
    | FmTrue ->
        true
    | FmApp(app) ->
        let provesApp (_ : string, q : Sort) =
            match q with
            | StProof(FmApp(app'), _) ->
                app' = app
            | _ ->
                false
        List.exists provesApp ctxt

let subStrSort (s1 : StrSort) (s2 : StrSort) : bool =
    match (s1, s2) with
    | (_, SsString) ->
        true
    | (SsLit(x1), SsLit(x2)) ->
        x1 = x2
    | (SsString, SsLit(_)) ->
        false

let sortCheckAtom (ctxt : SortContext) (atom : Atom) (rng : Range) : Check<Sort> =
    match atom with
    | AtomLit(str) ->
        Result (StStr(SsLit(str), noRange))
    | AtomVar(varName) ->
        match lookup ctxt varName with
        | Some(sort) ->
            Result sort
        | None ->
            Error [("Sort variable " + varName + " not in sorting context.", rng)]

/// Checks that app is a proposition: its predicate is applied to the right number of strings, each of
/// the right sort, and ctxt contains all of the proofs that the predicate's signature asks for.
let checkPredApp (ctxt : SortContext) (app : PredApp) (rng : Range) : Check<unit> =
    let checkArg (arg : Atom) ((formalName, formalSort) : string * StrSort) : Check<unit> =
        check {
            let! argSort = sortCheckAtom ctxt arg rng
            do!
                match argSort with
                | StStr(strSort, _) when subStrSort strSort formalSort ->
                    Result ()
                | _ ->
                    Error [("Argument " + arg.String + " of " + app.pred + " has sort " + argSort.String
                            + ", which does not match the sort " + formalSort.String + " of " + formalName, rng)]
        }

    let checkProof (proof : PredApp) : Check<unit> =
        match proves ctxt (FmApp proof) with
        | true ->
            Result ()
        | false ->
            Error [("Proof of " + proof.String + " not in context.", rng)]

    check {
        let! predSig =
            match lookup ctxt app.pred with
            | Some(StPred(predSig, _)) ->
                Result predSig
            | Some(sort) ->
                Error [("Expected " + app.pred + " to be a predicate. Instead it has the sort " + sort.String, rng)]
            | None ->
                Error [("Sort variable " + app.pred + " not in sorting context.", rng)]
        do!
            match app.args.Length = predSig.strings.Length with
            | true ->
                Result ()
            | false ->
                Error [(sprintf "%s takes %d string argument(s), but is applied to %d in %s"
                                app.pred predSig.strings.Length app.args.Length app.String, rng)]
        do! doAll <| List.map2 checkArg app.args predSig.strings
        do! doAll <| List.map checkProof (predSig.instantiate app.args)
    }

let checkFormula (ctxt : SortContext) (formula : Formula) (rng : Range) : Check<unit> =
    match formula with
    | FmTrue ->
        Result ()
    | FmApp(app) ->
        checkPredApp ctxt app rng

let wfSort (ctxt : SortContext) (sort : Sort) : Check<unit> =
    match sort with
    | StStr(_, _) ->
        Result ()
    | StProof(formula, rng) ->
        withError (formula.String + " failed to sort check.") rng <| checkFormula ctxt formula rng
    | StPred(predSig, rng) ->
        let predSig' = enterPredSig ctxt predSig
        let ctxtWithStrings =
            List.fold (fun ctxt' (x, strSort) -> (x, StStr(strSort, noRange)) :: ctxt') ctxt predSig'.strings
        /// each proposition of the proof section may rely on proofs of the ones that precede it
        let checkProofFormal (ctxt' : SortContext) (app : PredApp) : Check<SortContext> =
            check {
                do! withError (app.String + " failed to sort check.") rng <| checkPredApp ctxt' app rng
                return ("_", StProof(FmApp app, noRange)) :: ctxt'
            }
        check {
            do!
                match List.length (List.distinct predSig.formalNames) = predSig.strings.Length with
                | true ->
                    Result ()
                | false ->
                    Error [("The string formals of " + predSig.String + " must have distinct names.", rng)]
            let! _ = foldM ctxtWithStrings checkProofFormal predSig'.proofs
            return ()
        }

let rec wfSortContext (ctxt : SortContext) : Check<unit> =
    match ctxt with
    | (var, st) :: rest ->
        check {
            do! wfSort rest st
            // todo: check that satellites s are well formed
            do! wfSortContext rest
        }
    | [] ->
        Result ()
