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

/// A chain of dictionaries, one for each key. The guards may mention every key, so they belong to
/// the innermost dictionary.
let rec makeDictChain (keys : List<string * StrSort>) (guards : Guards) (codTy : Ty) (rng : Range) =
    match keys with
    | [(varName, sort)] ->
        TyDict(varName, sort, guards, codTy, rng)
    | (varName, sort) :: restKeys ->
        TyDict(varName, sort, [], makeDictChain restKeys guards codTy rng, rng)
    | [] ->
        codTy

/// create a chain of dictionaries whose keys are bounded by an anonymous predicate
let makeAnonDictChain (keys : List<string * StrSort>) (codTy : Ty) (rng : Range) =

    /// the sort of the predicate bounding the dictionary chain's keys
    let predSt = StPred(makePredSig keys [], noRange)

    /// the anonymous predicate, applied to the keys
    let predApp = makePredApp "***" (List.map (fun (varName, _) -> AtomVar varName) keys)

    TyUnion(TyIndAbs("***", predSt, makeDictChain keys [(FmApp predApp, rng)] codTy rng, rng), rng)
