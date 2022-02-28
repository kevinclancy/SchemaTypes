module Eval

open Syntax
open Utils

let rec applyProofs (sctxt : SortContext) (ty : Ty) : Ty =
    match ty with
    | TyIndAbs(varName, StProof(ind, _), codTy, rng) ->
        let provesInd (a : string, q : Sort) =
            match q with
            | StProof(j, _) when ind.IndexEquals(j) ->
                true
            | _ ->
                false
        match List.tryFind provesInd sctxt with
        | Some(a, StProof(j, _)) ->
            applyProofs sctxt codTy
        | Some(_, _) ->
            failwith "impossible"
        | None ->
            ty
    | _ ->
        ty

let rec step (sctxt : SortContext) (ty : Ty) : Option<Ty> =
    match ty with
    | TyDict(keyVarName, keySort, domTy, rng) ->
        let sctxt' = (keyVarName, keySort) :: sctxt
        Option.map (fun domTy' -> TyDict(keyVarName, keySort, domTy', rng))
                   (step sctxt' domTy)
    | TyRecord(fields, rng) ->
        let sctxtWithStr (x : string) =
            ("_" , StStringLit(x, noRange)) :: sctxt
        let rec stepFields (fields : List<string * Ty>) : Option<List<string * Ty>> =
            match fields with
            | (nm, ty) :: rest when (step (sctxtWithStr nm) ty).IsSome ->
                Some <| (nm, (step (sctxtWithStr nm) ty).Value) :: rest
            | (nm, ty) :: rest ->
                match stepFields rest with
                | Some rest' ->
                    Some <| (nm, ty) :: rest'
                | None ->
                    None
            | [] ->
                None
        Option.map (fun fields' -> TyRecord(fields', rng))
                   (stepFields fields)
    | TyStringRef(_, _, _, _) ->
        None
    | TyIndAbs(varName, domSort, codTy, rng) ->
        let sctxt' = (varName, domSort) :: sctxt
        Option.map (fun codTy' -> TyIndAbs(varName, domSort, codTy', rng))
                   (step sctxt' codTy)
    | TyTyAbs(varName, domKind, codTy, rng) ->
        Option.map (fun codTy' -> TyTyAbs(varName, domKind, codTy', rng)) 
                   (step sctxt codTy)
    | TyUnion(indTyFun, rng) ->
        Option.map (fun indTyFun' -> TyUnion(indTyFun', rng))
                   (step sctxt indTyFun)
    | TyTyApp(fn, arg, rng) ->
        match step sctxt fn with
        | Some fn' ->
            Some <| TyTyApp(fn', arg, rng)
        | None ->
            match step sctxt arg with
            | Some arg' ->
                Some <| TyTyApp(fn, arg', rng)
            | None ->
                match fn with
                | TyTyAbs(boundVarName, domKind, codTy, rng') ->
                    Some <| codTy.substTy(boundVarName, arg)
                | _ ->
                    None
    | TyIndApp(fn, arg, rng) ->
        match step sctxt fn with
        | Some fn' ->
            Some <| TyIndApp(fn', arg, rng)
        | None ->
            match fn with
            | TyIndAbs(boundVarName, domSort, codTy, rng') ->
                let codTy' = codTy.substInd(boundVarName, arg)
                Some <| applyProofs sctxt codTy'
            | _ ->
                None
    | TyVar(_, _) ->
        None
    | TyLet(varName, rhs, body, rng) ->
        match step sctxt rhs with
        | Some rhs' ->
            Some <| TyLet(varName, rhs', body, rng)
        | None ->
            Some <| body.substTy(varName, rhs)

let rec normalize (sctxt : SortContext) (ty : Ty) : Ty =
    let steps = Seq.unfold (fun x -> match step sctxt x with None -> None | Some x' -> Some (x' , x')) ty
    List.last (ty :: (List.ofSeq steps))
        
type Ty with
    member this.IsNormalized(sctxt : SortContext) =
        match step sctxt this with
        | Some(_) ->
            false
        | None ->
            true
