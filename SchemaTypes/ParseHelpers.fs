module ParseHelpers

open Utils
open Surface.Syntax

let makePredApp (pred : string) (args : List<Atom>) : PredApp =
    { pred = pred ; args = args }

/// The signature of the n-ary predicates whose string formals are *strings* and which require proofs of *proofs*
let makePredSig (strings : List<string * StrSort>) (proofs : List<PredApp>) : PredSig =
    { strings = strings ; proofs = proofs }

/// A block of predicate definitions whose scope is *body*. Each predicate is also in scope
/// in the definitions that follow it.
let makePredicates (defs : List<string * Sort>) (body : Ty) (rng : Range) : Ty =
    List.foldBack (fun (name, sort) scope -> TyUnion(TyIndAbs(name, sort, scope, rng), rng)) defs body

let rec makeDictDom (guards : List<Formula * Range>) (domTy : Ty) =
    match guards with
    | (formula, rng) :: rest ->
        TyUnion(TyIndAbs("***", StProof(formula, rng), makeDictDom rest domTy , noRange), noRange)
    | [] ->
        domTy

let rec makeDictChain (domSorts : List<string * StrSort>) (codTy : Ty) (rng : Range) =
    match domSorts with
    | (varName, sort) :: restCods ->
        TyDict(varName, sort, makeDictChain restCods codTy rng, rng)
    | [] ->
        codTy

/// create a chain of dictionaries whose keys are bounded by an anonymous predicate
let makeAnonDictChain (domSorts : List<string * StrSort>) (codTy : Ty) (rng : Range) =

    /// the sort of the predicate bounding the dictionary chain's keys
    let predSt = StPred(makePredSig domSorts [], noRange)

    /// the anonymous predicate, applied to the keys
    let predApp = makePredApp "***" (List.map (fun (varName, _) -> AtomVar varName) domSorts)

    let rec makeAnonDictChainAux (domSorts : List<string * StrSort>) : Ty  =
        match domSorts with
        | (varName, sort) :: restDoms ->
            TyDict(varName, sort, makeAnonDictChainAux restDoms, rng)
        | [] ->
            TyUnion(TyIndAbs("***", StProof(FmApp predApp, noRange), codTy, rng), rng)

    TyUnion(TyIndAbs("***", predSt, makeAnonDictChainAux domSorts, rng), rng)
