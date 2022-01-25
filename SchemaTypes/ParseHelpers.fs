module ParseHelpers

open Utils
open Syntax

let rec makeDictDom (guards : List<Index>) (domTy : Ty) =
    match guards with
    | ind :: rest ->
        TyUnion(TyIndAbs("***", StProof(ind, noRange), makeDictDom rest domTy , noRange), noRange)
    | [] ->
        domTy
