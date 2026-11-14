module DecisionProcedures

open Surface.Syntax

/// Converts a sort context into an equivalent canonical sort context, which lists the context's
/// predicates, strings, and proofs in separate sections.
let canonicalize (ctxt : SortContext) : CanonicalSortContext =
    let rec canonicalizeAux (ctxt : SortContext)
                            (result : CanonicalSortContext) : CanonicalSortContext =
        match ctxt with
        | (varName, StStr(srt, _)) :: rest ->
            canonicalizeAux rest { result with strings = (varName, srt) :: result.strings }
        | (varName, StPred(predSig, _)) :: rest ->
            canonicalizeAux rest { result with predicates = (varName, predSig) :: result.predicates }
        | (_, StProof(formula, _)) :: rest ->
            let result' =
                match formula with
                | FmTrue ->
                    result
                | FmApp(app) ->
                    { result with proofs = result.proofs.Add app }
            canonicalizeAux rest result'
        | [] ->
            result
    canonicalizeAux ctxt CanonicalSortContext.empty

type SubstitutionStatus =
    | Substituted
    | NotSubstituted

/// A predicate application of a decision procedure, which we are trying to match
/// against the predicate applications that are proven at a validation site
type PredAppTarget = {
    /// name of the predicate
    predicate : string

    /// First component - the argument
    /// Second component - NotSubstituted if the argument is a string variable of the decision procedure,
    ///                    Substituted if it has been replaced with an argument from the validation site.
    ///                    String literals mean the same thing on both sides, so they count as Substituted.
    args : List<Atom * SubstitutionStatus>
}
    with
        member this.subst(p : Map<string, Atom>) =
            let mapArg ((arg, status) : Atom * SubstitutionStatus) : Atom * SubstitutionStatus =
                match (arg, status) with
                | (AtomVar(varName), NotSubstituted) when p.ContainsKey varName ->
                    (p.[varName], Substituted)
                | _ ->
                    (arg, status)

            { this with predicate = this.predicate ; args = List.map mapArg this.args }

        static member ofPredApp (app : PredApp) =
            let ofArg (arg : Atom) : Atom * SubstitutionStatus =
                match arg with
                | AtomVar(_) ->
                    (arg, NotSubstituted)
                | AtomLit(_) ->
                    (arg, Substituted)

            { predicate = app.pred ; args = List.map ofArg app.args }


/// the state of the algorithm that instantiates decision procedures
type InstantiationState = {
    substitutions : Map<string, Atom>
    proofs : Set<PredAppTarget>
}
    with
        static member ofSortContext (ctxt : CanonicalSortContext) =
            { substitutions = Map.empty ; proofs = Set.map PredAppTarget.ofPredApp ctxt.proofs }

let appMatches (source : PredApp) (target : PredAppTarget) =

    /// sourceArg - the argument we are trying to use as an instantiator
    /// targetArg - first component is the argument, second component tells whether it has already been instantiated
    let argMatches (sourceArg : Atom) (targetArg : Atom * SubstitutionStatus) =
        match targetArg with
        | (_, NotSubstituted) ->
            true
        | (arg, Substituted) when arg = sourceArg ->
            true
        | _ ->
            false

    source.pred = target.predicate
    && source.args.Length = target.args.Length
    && List.forall2 argMatches source.args target.args

let getSubstitutions (subst : Map<string, Atom>) (source : PredApp) (target : PredAppTarget) : Map<string, Atom> =
    let accSubst (substitutions : Map<string, Atom>) (sourceArg : Atom) (targetArg : Atom * SubstitutionStatus) =
        match targetArg with
        | (AtomVar(targetArgName), NotSubstituted) ->
            substitutions.Add(targetArgName, sourceArg)
        | _ ->
            substitutions

    List.fold2 accSubst subst source.args target.args

/// Finds a substitution of the site's arguments for the decision procedure's string variables under which
/// each of the decision procedure's proofs is one of siteProofs
let rec private instantiateAux (siteProofs : Set<PredApp>) (state : InstantiationState) : Option<Map<string, Atom>> =

    System.Console.WriteLine(state.substitutions)

    match Set.isEmpty state.proofs with
    | true ->
        Some <| state.substitutions
    | false ->
        let targetApp = state.proofs.MinimumElement
        let candidates = Set.filter (fun x -> appMatches x targetApp) siteProofs
        let tryCandidate(candidate : PredApp) : Option<Map<string,Atom>> =
            let substitutions' = getSubstitutions state.substitutions candidate targetApp
            let proofs' = Set.map (fun (x : PredAppTarget) -> x.subst substitutions') <| state.proofs.Remove targetApp
            instantiateAux siteProofs { substitutions = substitutions' ; proofs = proofs' }

        Seq.tryPick tryCandidate (Set.toSeq candidates)

/// The lookups that decide the decision procedure's proofs, as instantiated by substitution.
/// selfVar is the site's refinement variable, if it has one.
/// Returns None if one of the decision procedure's strings has not been instantiated: none of its proofs
/// mention that string, so we don't know which key to look up in its position.
let private instantiateKeys (decisionProcedure : CanonicalSortContext)
                            (substitution : Map<string, Atom>)
                            (selfVar : Option<string>) : Option<List<DecisionProcedureKey>> =
    let mapStringVar ((name, sort) : string * StrSort) : Option<DecisionProcedureKey> =
        match sort with
        | SsString ->
            match substitution.TryFind name with
            | Some(AtomVar(varName)) when Some varName = selfVar ->
                Some <| ArgumentKey("@loc")
            | Some(AtomVar(varName)) ->
                Some <| ArgumentKey(varName)
            | Some(AtomLit(str)) ->
                Some <| LiteralKey(str)
            | None ->
                None
        | SsLit(str) ->
            Some <| LiteralKey(str)

    let keys = List.map mapStringVar decisionProcedure.strings
    match List.forall Option.isSome keys with
    | true ->
        Some <| List.map Option.get keys
    | false ->
        None

/// Instantiates a decision procedure using the site context, or reports None if impossible
let instantiate (siteContext : CanonicalSortContext) (decisionProcedure : CanonicalSortContext) : Option<List<DecisionProcedureKey>> =

    System.Console.WriteLine("***")
    System.Console.WriteLine("site context: " + siteContext.String + "\n\nDecision procedure: " + decisionProcedure.String + "\n")

    let keys =
        instantiateAux siteContext.proofs (InstantiationState.ofSortContext decisionProcedure)
        |> Option.bind (fun substitution -> instantiateKeys decisionProcedure substitution None)

    match keys with
    | Some _ ->
        System.Console.WriteLine("instantiation succeeded")
        System.Console.WriteLine("***")
        // substitute into siteContext.strings - there is no longer a need for the "wildcard" decision procedure key type
        keys
    | None ->
        System.Console.WriteLine("instaniation failed")
        System.Console.WriteLine("***")
        None

/// Instantiates a decision procedure using the site context, or reports None if impossible
let instantiate2 (siteContext : DecisionSite) (decisionProcedure : CanonicalSortContext) : Option<List<DecisionProcedureKey>> =

    let siteProofs = Set.add siteContext.formulaToDecide siteContext.sctxt.proofs

    System.Console.WriteLine("***")
    System.Console.WriteLine("site context: " + siteContext.String + "\n\nDecision procedure: " + decisionProcedure.String + "\n")

    // if dp doesn't contain formula matching the one to decide, instantiation fails
    let predMatches (i : PredApp) (j : PredApp) =
        i.pred = j.pred

    let keys =
        match Set.exists (predMatches siteContext.formulaToDecide) decisionProcedure.proofs with
        | true ->
            instantiateAux siteProofs (InstantiationState.ofSortContext decisionProcedure)
            |> Option.bind (fun substitution -> instantiateKeys decisionProcedure substitution (Some siteContext.selfVar))
        | false ->
            None

    match keys with
    | Some _ ->
        System.Console.WriteLine("instantiation succeeded")
        System.Console.WriteLine("***")
        // substitute into siteContext.strings - there is no longer a need for the "wildcard" decision procedure key type
        keys
    | None ->
        System.Console.WriteLine("instaniation failed")
        System.Console.WriteLine("***")
        None




//let addDecisionProcedure2 (ctxt : SortContext) (ind : Index) : SortContext =
//    assert (
//        let x = sortCheckInd ctxt ind
//        x.Succeeds && match x.GetResult with | StProp(_) -> true | _ -> false
//    )    

//    match ind with
//    | FlatApp(fn, args) ->
//        let initialVarSet = Set.add fn (Set.ofList args)

//        let addEntry (targetCtxt : SortContext) (propSet : Set<Index>) (varSet : Set<string>) : SortContext =
//            assert ((Set.unionMany <| Set.map (fun (x : Index) -> x.freeVars) propSet) = varSet)

//            match targetCtxt with
//            | (varName, StFun(_,_,_,_) as sort, satellites, entryType) as first :: rest when varSet.Contains varName ->
//                (varName, sort, satellites.Add <| DecisionProcedure (fn, makePath ctxt args))
//            | (varName, sort, satellites, entryType) as first :: rest ->
//                match Set.intersect sort.freeVars (Set.unionMany <| Set.map (fun (x : Index) -> x.freeVars) propSet) with
//                | Set.empty ->
//                    first :: addEntry 
//                | intersection ->
                    
//let addDecisionProcedure (ctxt : SortContext) (ind : Index) : SortContext =
//    assert (
//        let x = sortCheckInd ctxt ind
//        x.Succeeds && match x.GetResult with | StProp(_) -> true | _ -> false
//    )

//    match ind with
//    | FlatApp(fn, args) ->
//        let rec makePath (ctxt : SortContext) (args : List<string>) : List<DecisionProcedureKey> =
//            match ctxt with
//            | (_, _, _, CStandard) :: rest ->
//                makePath rest args
//            | (_, StStringLit(s,_), _, CPhysical) :: rest ->
//                LiteralKey s :: makePath rest args
//            | (varName, StString(_), _, CPhysical) :: rest ->
//                match List.tryFindIndex (fun x -> x = varName) args with
//                | Some n ->
//                    ArgumentKey n :: makePath rest args
//                | None ->
//                    WildcardKey :: makePath rest args
//            | [] ->
//                []
//            | _ ->
//                failwith "unreachable"

//        let indDependsOnEntry (varName : string, sort : Sort, satellites : Set<Satellite>, entryType : EntryType) =
//            varName = fn || (not <| Set.isEmpty (Set.intersect sort.freeVars (Set.ofSeq (List.toSeq args))))

//        let rec add (targetCtxt : SortContext) : SortContext =
//            match targetCtxt with
//            | (varName, sort, satellites, entryType) as first :: rest ->
//                match indDependsOnEntry (varName, sort, satellites, entryType) with
//                | true ->
//                    (varName, sort, satellites.Add <| DecisionProcedure (fn, makePath ctxt args), entryType) :: rest
//                | false ->
//                    first :: add rest
//            | [] ->
//                failwith "unreachable if the index is well sorted in the context"

//        add ctxt
//    | _ ->
//        ctxt