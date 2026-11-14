module Surface.Eval

open Surface.Syntax
open Surface.SortCheck
open Utils

let rec applyProofs (sctxt : SortContext) (ty : Ty) : Ty =
    match ty with
    | TyIndAbs(_, StProof(formula, _), codTy, _) when proves sctxt formula ->
        applyProofs sctxt codTy
    | _ ->
        ty

let rec step (sctxt : SortContext) (ty : Ty) : Option<Ty> =
    match ty with
    | TyDict(keyVarName, keySort, guards, domTy, rng) ->
        let keyVarName, guards, domTy = enterDict sctxt keyVarName guards domTy
        let sctxt' = dictContext sctxt keyVarName keySort guards
        Option.map (fun domTy' -> TyDict(keyVarName, keySort, guards, domTy', rng))
                   (step sctxt' domTy)
    | TyRecord(fields, rng) ->
        let sctxtWithStr (x : string) =
            ("_" , StStr(SsLit(x), noRange)) :: sctxt
        let rec stepFields (fields : List<string * Ty>) : Option<List<string * Ty>> =
            match fields with
            | (nm, ty) :: rest ->
                match step (sctxtWithStr nm) ty with
                | Some ty' ->
                    Some <| (nm, ty') :: rest
                | None ->
                    Option.map (fun rest' -> (nm, ty) :: rest') (stepFields rest)
            | [] ->
                None
        Option.map (fun fields' -> TyRecord(fields', rng))
                   (stepFields fields)
    | TyStringRef(_, _, _, _) ->
        None
    | TyIndAbs(varName, domSort, codTy, rng) ->
        let varName, codTy = enterTy sctxt varName codTy
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
