module Eval

open Syntax

let rec step (ty : Ty) : Option<Ty> =
    match ty with
    | TyDict(keyVarName, keySort, domTy, rng) ->
        Option.map (fun domTy' -> TyDict(keyVarName, keySort, domTy', rng))
                   (step domTy)
    | TyRecord(fields, rng) ->
        let rec stepFields (fields : List<string * Ty>) : Option<List<string * Ty>> =
            match fields with
            | (nm, ty) :: rest when (step ty).IsSome ->
                Some <| (nm, (step ty).Value) :: rest
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
        Option.map (fun codTy' -> TyIndAbs(varName, domSort, codTy', rng))
                   (step codTy)
    | TyTyAbs(varName, domKind, codTy, rng) ->
        Option.map (fun codTy' -> TyTyAbs(varName, domKind, codTy', rng)) 
                   (step codTy)
    | TyUnion(indTyFun, rng) ->
        Option.map (fun indTyFun' -> TyUnion(indTyFun', rng))
                   (step indTyFun)
    | TyTyApp(fn, arg, rng) ->
        match step fn with
        | Some fn' ->
            Some <| TyTyApp(fn', arg, rng)
        | None ->
            match step arg with
            | Some arg' ->
                Some <| TyTyApp(fn, arg', rng)
            | None ->
                match fn with
                | TyTyAbs(boundVarName, domKind, codTy, rng') ->
                    Some <| codTy.substTy(boundVarName, arg)
                | _ ->
                    None
    | TyIndApp(fn, arg, rng) ->
        match step fn with
        | Some fn' ->
            Some <| TyIndApp(fn', arg, rng)
        | None ->
            match fn with
            | TyIndAbs(boundVarName, domSort, codTy, rng') ->
                Some <| codTy.substInd(boundVarName, arg)
            | _ ->
                None
    | TyVar(_, _) ->
        None
    | TyLet(varName, rhs, body, rng) ->
        match step rhs with
        | Some rhs' ->
            Some <| TyLet(varName, rhs', body, rng)
        | None ->
            Some <| body.substTy(varName, rhs)

    
