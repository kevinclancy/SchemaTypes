module ParseHelpers

open Utils
open Surface.Syntax

let makePredApp (pred : string) (args : List<Atom>) : PredApp =
    { pred = pred ; args = args }

/// The sort of the n-ary predicates whose string formals are *strings* and which require proofs of *proofs*
let makePredSort (strings : List<string * StrSort>) (proofs : List<PredApp>) (rng : Range) : Sort =
    StPred({ strings = strings ; proofs = proofs }, rng)

/// The string formals of a predicate must have string sorts
let toStrSort (sort : Sort) : StrSort =
    match sort with
    | StStr(strSort, _) ->
        strSort
    | _ ->
        failwith ("expected a string sort, but found " + sort.String)

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
    let predSt = makePredSort domSorts [] noRange

    /// the anonymous predicate, applied to the keys
    let predApp = makePredApp "***" (List.map (fun (varName, _) -> AtomVar varName) domSorts)

    let rec makeAnonDictChainAux (domSorts : List<string * StrSort>) : Ty  =
        match domSorts with
        | (varName, sort) :: restDoms ->
            TyDict(varName, sort, makeAnonDictChainAux restDoms, rng)
        | [] ->
            TyUnion(TyIndAbs("***", StProof(FmApp predApp, noRange), codTy, rng), rng)

    TyUnion(TyIndAbs("***", predSt, makeAnonDictChainAux domSorts, rng), rng)
