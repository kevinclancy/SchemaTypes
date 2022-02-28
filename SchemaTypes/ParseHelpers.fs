module ParseHelpers

open Utils
open Syntax

let rec makeDictDom (guards : List<Index>) (domTy : Ty) =
    match guards with
    | ind :: rest ->
        TyUnion(TyIndAbs("***", StProof(ind, noRange), makeDictDom rest domTy , noRange), noRange)
    | [] ->
        domTy

let rec makeDictChain (codSorts : List<string * Sort>) (domTy : Ty) (rng : Range) =
    match codSorts with
    | (varName, sort) :: restCods ->
        TyDict(varName, sort, makeDictChain restCods domTy rng, rng)
    | [] ->
        domTy