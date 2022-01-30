module KindCheck

open Syntax
open SortCheck
open CheckComputation

let rec applyProofs (ctxt : SortContext) (kind : Kind) : Check<Kind> =
    match kind with
    | KIndFun(varName, StProof(ind,prfRng), cod, rng) ->
        let provesInd (a : string, q : Sort, s : Set<Satellite>) =
            match q with
            | StProof(j, _) when ind.IndexEquals(j) ->
                true
            | _ ->
                false
        match List.tryFind provesInd ctxt with
        | Some(a, StProof(j, _), _) ->
            applyProofs ctxt (cod.subst(IndVar(a,noRange), varName))    
        | Some(_,_,_) ->
            failwith "impossible"
        | None ->
            Error [("Proof of " + ind.ToString() + " not in context.", noRange)]
    | _ ->
        Result kind

let rec subSort (sctxt : SortContext) (s1 : Sort) (s2 : Sort) = 
    match (s1, s2) with
    | (StString(_), StString(_))
    | (StStringLit(_,_), StString(_)) ->
        true
    | (StStringLit(x1,_),StStringLit(x2,_)) when x1 = x2 ->
        true
    | (StProp(_), StProp(_)) ->
        true
    | (StProof(ind1,_), StProof(ind2,_)) ->
        false
    | (StFun(varName1, domSort1, codSort1, _), StFun(varName2, domSort2, codSort2, _)) ->
        let domSub = subSort sctxt domSort2 domSort1
        let sctxt' = (varName2, domSort2, Set.empty) :: sctxt 
        let codSub = subSort sctxt' (codSort1.subst(IndVar(varName2, noRange), varName1)) codSort2
        domSub && codSub
    | _ ->
        false

let checkSubSort (sctxt : SortContext) (s1 : Sort) (s2 : Sort) : Check<Unit> =
    match subSort sctxt s1 s2 with
    | true ->
        Result ()
    | false ->
        Error []

let rec subKind (sctxt : SortContext) (k1 : Kind) (k2 : Kind) : bool =
    match (k1, k2) with
    | (KProper(_), KProper(_)) ->
        true
    | (KProperPopulated(_), KProper(_)) ->
        true
    | (KTyFun(dom1,cod1,_), KTyFun(dom2,cod2,_)) ->
        (subKind sctxt dom2 dom1) && (subKind sctxt cod1 cod2)
    | (KIndFun(var1, dom1,cod1,_), KIndFun(var2, dom2, cod2,_)) ->
        let sctxt' = (var2, dom2, Set.empty) :: sctxt
        (subSort sctxt dom2 dom1) && (subKind sctxt' cod1 cod2)
    | _ ->
        false

let checkSubKind (sctxt : SortContext) (k1 : Kind) (k2 : Kind) : Check<unit> =
    match subKind sctxt k1 k2 with
    | true ->
        Result ()
    | false ->
        Error []

let rec wfKind (sctxt : SortContext) (k : Kind) : Check<unit> =
    match k with
    | KProper(_)
    | KProperPopulated(_) ->
        Result ()
    | KTyFun(dom, cod, _) ->
        check {
            do! wfKind sctxt dom
            do! wfKind sctxt cod
        }
    | KIndFun(varName, dom, cod, _) ->
        check {
            do! wfSort sctxt dom
            let sctxt' = (varName, dom, Set.empty) :: sctxt
            do! wfKind sctxt' cod
        }

let rec kindCheck (sctxt : SortContext) (kctxt : KindContext) (subject : Ty) (target : Kind) : Check<Kind> =
    check {
        let! kind = kindSynth sctxt kctxt subject
        do! withError ("type " + subject.ToString() + "'s kind " + kind.ToString() + " is not a subkind of " + target.ToString())  
                      subject.Range
                      (checkSubKind sctxt kind target)
        return kind
    }

and kindSynth (sctxt : SortContext) (kctxt : KindContext) (ty : Ty) : Check<Kind> =
    match ty with
    | TyDict(keyVarName, keySort, domTy, rng) -> 
        check {
            do! withError "expected string sort for dictionary key" 
                          keySort.Range 
                          (checkSubSort sctxt keySort (StString(noRange)))
            let sctxt' = (keyVarName, keySort, Set.empty) :: sctxt
            let! domKind = kindSynth sctxt' kctxt domTy
            do! withError "expected proper kind for dictionary value" 
                          domTy.Range
                          (checkSubKind sctxt' domKind (KProper(noRange)))
            // we can't return KProperPopulated because we don't know if it contains any entries
            return (KProper(noRange))
        }
    | TyRecord(fields, rng) ->
        let checkField ((name,ty) : string * Ty) : Check<Kind> =
            kindCheck sctxt kctxt ty (KProper(noRange))
        let isPopulated (kind : Kind) : bool =
            match kind with
            | KProperPopulated(_) ->
                true
            | _ ->
                false
        check {
            let! allKinds = letAll <| List.map checkField fields
            return (if List.exists isPopulated allKinds then KProperPopulated(noRange) else KProper(noRange))
        }
    | TyStringRef(varName, sort, formula, rng) ->
        check {
            let sctxt' = (varName, sort, Set.empty) :: sctxt
            let! indSort = sortCheckInd sctxt' formula
            do! withError ("sort of index " + formula.String + "is not prop") 
                          formula.Range 
                          (checkSubSort sctxt' indSort (StProp(noRange)))
            return KProperPopulated(noRange)
        }
    | TyIndAbs(varName, domSort, codTy, rng) ->
        check {
            do! wfSort sctxt domSort
            let sctxt' = (varName, domSort, Set.empty) :: sctxt
            let! codKind = kindSynth sctxt' kctxt codTy
            return KIndFun(varName, domSort, codKind, noRange)
        }
    | TyTyAbs(varName, domKind, codTy, rng) ->
        check {
            do! wfKind sctxt domKind
            let kctxt' = kctxt.Add(varName,domKind)
            let! codKind = kindSynth sctxt kctxt' codTy
            return KTyFun(domKind, codKind, noRange)
        }
    | TyUnion(indTyFun, rng) ->
        check {
            let! kFun = kindSynth sctxt kctxt indTyFun
            do! 
                match kFun with
                | KIndFun(_, _, kCod, _) ->
                    withError "expected codomain to be a proper type" 
                              kCod.Range
                              (checkSubKind sctxt kCod (KProper(noRange)))
                | _ ->
                    Error [("Unions can only be taken over index abstractions, not types of kind " + kFun.ToString(), rng)] 
            return KProper(noRange)
        }
    | TyTyApp(fn, arg, rng) ->
        check {
            let! kArg = kindSynth sctxt kctxt arg
            let! kFun = kindSynth sctxt kctxt fn
            let! kCod = 
                match kFun with
                | KTyFun(kDom, kCod, rng) ->
                    check {
                        do! withError ("type " + arg.ToString() + "'s kind " + kArg.ToString() + " is not a subkind of " + kDom.ToString())
                                      rng
                                      (checkSubKind sctxt kArg kDom)
                        return kCod
                    }
                | _ ->
                    Error [("expected " + fn.ToString() + " to be a type function. Instead, it has kind " + kFun.ToString(), rng)]
            return kCod
        }
    | TyIndApp(fn, arg, rng) ->
        check {
            let! sArg = sortCheckInd sctxt arg
            let! kFun = kindSynth sctxt kctxt fn
            let! kRes =
                match kFun with
                | KIndFun(varName, sDom, kCod, rng) ->
                    check {
                        do! withError ("type " + arg.ToString() + "'s sort " + sArg.ToString() + " is not a subsort of " + sDom.ToString())
                                      rng
                                      (checkSubSort sctxt sArg sDom)
                        return kCod.subst(arg, varName)
                    }
                | _ ->
                    Error [("Expected " + fn.ToString() + " to be an index abstraction, but instead it has kind " + kFun.ToString(), fn.Range)]
            let! kRes' = applyProofs sctxt kRes
            return kRes'
        }
    | TyVar(name, rng) ->
        check {
            let! kind = 
                match kctxt.TryFind name with
                | Some(kind) ->
                    Result kind
                | None ->
                    Error [("Type variable named " + name + " not found in context.", rng)]
            return kind
        }
    | TyLet(varName, rhs, body, rng) ->
        check {
            let! kRhs = kindSynth sctxt kctxt rhs
            let kctxt' = kctxt.Add(varName, kRhs)
            let! kRes = kindSynth sctxt kctxt' body
            return kRes
        }