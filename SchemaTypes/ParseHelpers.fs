module ParseHelpers

open Utils
open Syntax

let rec makeDictDom (guards : List<Index>) (domTy : Ty) =
    match guards with
    | ind :: rest ->
        TyUnion(TyIndAbs("***", StProof(ind, noRange), makeDictDom rest domTy , noRange), noRange)
    | [] ->
        domTy

let rec makeDictChain (domSorts : List<string * Sort>) (codTy : Ty) (rng : Range) =
    match domSorts with
    | (varName, sort) :: restCods ->
        TyDict(varName, sort, makeDictChain restCods codTy rng, rng)
    | [] ->
        codTy

/// create a chain of dictionaries whose keys are bounded by an anonymous predicate
let makeAnonDictChain (domSorts : List<string * Sort>) (codTy : Ty) (rng : Range) =
    
    let rec makePredSt (domSorts : List<string * Sort>) (app : Index) : Sort * Index =
        match domSorts with
        | (varName, sort) :: restDoms ->
            let predSt, predApp = makePredSt restDoms (IndApp(app, IndVar(varName, noRange), noRange))
            StFun(varName, sort, predSt, noRange), predApp
        | [] ->
            StProp(noRange), app

    let predSt, predApp = makePredSt domSorts (IndVar("***", noRange))

    /// returns (dictChainTy, predSt) where
    ///
    /// dictChainTy - the typeof the dictionary chain
    /// predSt - the sort of the predicate bounding the dictionary type's keys
    let rec makeAnonDictChainAux (domSorts : List<string * Sort>) : Ty  =
        match domSorts with
        | (varName, sort) :: restDoms ->
            TyDict(varName, sort, makeAnonDictChainAux restDoms, rng)
        | [] ->
            TyUnion(TyIndAbs("***", StProof(predApp, noRange), codTy, rng), rng)

    TyUnion(TyIndAbs("***", predSt, makeAnonDictChainAux domSorts, rng), rng)