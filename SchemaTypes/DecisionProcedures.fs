module DecisionProcedures

open Syntax
open SortCheck

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

/// converts a Sort Context into an equivalent canonical sort context
let canonicalize (ctxt : SortContext) : CanonicalSortContext =
    let rec canonicalizeAux (ctxt : SortContext) (result : CanonicalSortContext) : CanonicalSortContext =
        match ctxt with
        | (varName, (StString(_) as srt), _) :: rest
        | (varName, (StStringLit(_) as srt), _) :: rest ->
            canonicalizeAux rest { result with strings = (varName, srt) :: result.strings }
        | (varName, StProp(_), _) :: rest ->
            canonicalizeAux rest { result with props = result.props.Add varName }
        | (varName, (StFun(_, _, _, _) as srt), _) :: rest ->
            canonicalizeAux rest { result with predicates = (varName, srt) :: result.predicates }
        | (_, StProof(ind, rng), _) :: rest ->
            canonicalizeAux rest { result with proofs = result.proofs.Add ind }
        | [] ->
            result
    canonicalizeAux ctxt CanonicalSortContext.empty

type FlatApp = {
    /// name of the predicate
    predicate : string 

    /// arguments to flat predicate
    args : List<string>
}
    with
        static member ofIndex (ind : Index) =
            match ind with
            | FlatApp(predicate, args) ->
                { predicate = predicate ; args = args }
            | _ ->
                failwith "index is not a flat application"

type SubstitutionStatus =
    | Substituted
    | NotSubstituted

type FlatAppTarget = {
    /// name of the predicate
    predicate : string 

    /// First component - name of argument
    /// Second component - true if the argument originated from decision procedure, 
    ///                    false if it originated from the validation site
    args : List<string * SubstitutionStatus>
}
    with
        member this.subst(p : Map<string, string>) =
            let mapArg ((varName, status) : string * SubstitutionStatus) : string * SubstitutionStatus =
                match (p.ContainsKey varName, status) with
                | (true, NotSubstituted) ->
                    (p.[varName], Substituted)
                | _ ->
                    (varName, status)
                
            { this with predicate = this.predicate ; args = List.map mapArg this.args }

        static member ofIndex (ind : Index) =
            match ind with
            | FlatApp(predicate, args) ->
                { predicate = predicate ; args = List.map (fun x -> (x, NotSubstituted)) args }
            | _ ->
                failwith "index is not a flat application"


/// the state of the algorithm that instantiates decision procedures
type InstantiationState = {
    substitutions : Map<string, string>
    proofs : Set<FlatAppTarget>
}
    with
        static member ofSortContext (ctxt : CanonicalSortContext) =
            { substitutions = Map.empty ; proofs = Set.map FlatAppTarget.ofIndex ctxt.proofs }


/// Instantiates a decision procedure using the current sort context, or reports None if impossible
let instantiate (siteContext : CanonicalSortContext) (decisionProcedure : CanonicalSortContext) : Option<List<DecisionProcedureKey>> =
    
    let appMatches (source : FlatApp) (target : FlatAppTarget) =
        
        /// sourceArg - the name of the variable we are trying to use as an instantiator
        /// targetArg - first component is variable name, second component true iff it has already been instantiated
        let argMatches (sourceArg : string) (targetArg : string * SubstitutionStatus) = 
            match targetArg with
            | (_, NotSubstituted) ->
                true
            | (varName, Substituted) when varName = sourceArg ->
                true
            | _ ->
                false

        source.predicate = target.predicate && List.forall2 argMatches source.args target.args 

    let getSubstitutions (subst : Map<string, string>) (source : FlatApp) (target : FlatAppTarget) : Map<string, string> =
        let accSubst (substitutions : Map<string, string>) (sourceArg : string) (targetArg : string * SubstitutionStatus) =
            match targetArg with
            | (targetArgName, Substituted) ->
                substitutions
            | (targetArgName, NotSubstituted) ->
                substitutions.Add(sourceArg, targetArgName)

        List.fold2 accSubst subst source.args target.args

    let siteProofs = Set.map FlatApp.ofIndex siteContext.proofs

    let rec instantiateAux (state : InstantiationState) : Option<Map<string, string>> =
        match Set.isEmpty state.proofs with
        | true ->
            Some <| Map.empty
        | false ->
            let targetApp = state.proofs.MinimumElement
            let candidates = Set.filter (fun x -> appMatches x targetApp) siteProofs
            let tryCandidate(candidate : FlatApp) : Option<Map<string,string>> =
                let substitutions' = getSubstitutions state.substitutions candidate targetApp
                let proofs' = Set.map (fun (x : FlatAppTarget) -> x.subst substitutions') <| state.proofs.Remove targetApp                
                instantiateAux { substitutions = substitutions' ; proofs = proofs' }

            Seq.tryPick tryCandidate (Set.toSeq candidates) 
    
    match instantiateAux (InstantiationState.ofSortContext decisionProcedure) with
    | Some substitution ->
        let mapStringVar ((name, sort) : string * Sort) =
            match sort with
            | StString(_) ->
                ArgumentKey(substitution.[name])
            | StStringLit(str, _) ->
                LiteralKey(str)
            | _ ->
                failwith "unreachable"

        // substitute into siteContext.strings - there is no longer a need for the "wildcard" decision procedure key type
        Some <| List.map mapStringVar siteContext.strings
    | None ->
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