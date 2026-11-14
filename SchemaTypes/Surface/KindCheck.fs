module Surface.KindCheck

open Surface.Syntax
open Surface.SortCheck
open CheckComputation

let rec applyProofs (ctxt : SortContext) (kind : Kind) (rng : Range) : Check<Kind> =
    match kind with
    | KIndFun(_, StProof(formula,_), cod, _) ->
        match proves ctxt formula with
        | true ->
            // proofs are irrelevant, so there is nothing to substitute into the codomain
            applyProofs ctxt cod rng
        | false ->
            Error [("Proof of " + formula.String + " not in context.", rng)]
    | _ ->
        Result kind

/// p1 is a subsignature of p2 if a predicate with signature p1 can be used wherever one with
/// signature p2 is expected: it accepts at least the same strings, and requires the same proofs.
let subPredSig (p1 : PredSig) (p2 : PredSig) : bool =
    match p1.strings.Length = p2.strings.Length with
    | false ->
        false
    | true ->
        let stringsSub = List.forall2 (fun (_, st1) (_, st2) -> subStrSort st2 st1) p1.strings p2.strings
        // compare the proof sections under a common choice of names for the string formals
        let formals = List.map AtomVar <| freshVars (Set.union p1.freeVars p2.freeVars) p2.formalNames
        let proofsEqual = (Set.ofList <| p1.instantiate formals) = (Set.ofList <| p2.instantiate formals)
        stringsSub && proofsEqual

let subSort (s1 : Sort) (s2 : Sort) : bool =
    match (s1, s2) with
    | (StStr(strSort1,_), StStr(strSort2,_)) ->
        subStrSort strSort1 strSort2
    | (StProof(formula1,_), StProof(formula2,_)) ->
        formula1 = formula2
    | (StPred(predSig1,_), StPred(predSig2,_)) ->
        subPredSig predSig1 predSig2
    | _ ->
        false

let checkSubSort (s1 : Sort) (s2 : Sort) : Check<Unit> =
    match subSort s1 s2 with
    | true ->
        Result ()
    | false ->
        Error []

let rec subKind (k1 : Kind) (k2 : Kind) : bool =
    match (k1, k2) with
    | (KProper(_), KProper(_)) ->
        true
    | (KProperPopulated(_), KProper(_)) ->
        true
    | (KProperPopulated(_), KProperPopulated(_)) ->
        true
    | (KTyFun(dom1,cod1,_), KTyFun(dom2,cod2,_)) ->
        (subKind dom2 dom1) && (subKind cod1 cod2)
    | (KIndFun(var1, dom1,cod1,_), KIndFun(var2, dom2, cod2,_)) ->
        // compare the codomains under a common name for the bound variable
        let var = Utils.freshVar (Set.union cod1.freeIndVars cod2.freeIndVars) var2
        (subSort dom2 dom1) && (subKind (cod1.rename(var1, var)) (cod2.rename(var2, var)))
    | _ ->
        false

let checkSubKind (k1 : Kind) (k2 : Kind) : Check<unit> =
    match subKind k1 k2 with
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
        let varName, cod = enterKind sctxt varName cod
        check {
            do! wfSort sctxt dom
            let sctxt' = (varName, dom) :: sctxt
            do! wfKind sctxt' cod
        }

let rec kindCheck (sctxt : SortContext) (kctxt : KindContext) (subject : Ty) (target : Kind) : Check<Kind> =
    check {
        let! kind = kindSynth sctxt kctxt subject
        do! withError ("type " + subject.String + "'s kind " + kind.String + " is not a subkind of " + target.String)
                      subject.Range
                      (checkSubKind kind target)
        return kind
    }

and kindSynth (sctxt : SortContext) (kctxt : KindContext) (ty : Ty) : Check<Kind> =
    match ty with
    | TyDict(keyVarName, keySort, domTy, rng) ->
        let keyVarName, domTy = enterTy sctxt keyVarName domTy
        check {
            let sctxt' = (keyVarName, StStr(keySort, noRange)) :: sctxt
            let! domKind = kindSynth sctxt' kctxt domTy
            do! withError "expected proper kind for dictionary value"
                          domTy.Range
                          (checkSubKind domKind (KProper(noRange)))
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
        let varName, formula = enterFormula sctxt varName formula
        check {
            let sctxt' = (varName, StStr(sort, noRange)) :: sctxt
            do! withError (formula.String + " failed to sort check.")
                          rng
                          (checkFormula sctxt' formula rng)
            return KProperPopulated(noRange)
        }
    | TyIndAbs(varName, domSort, codTy, rng) ->
        let varName, codTy = enterTy sctxt varName codTy
        check {
            do! wfSort sctxt domSort
            let sctxt' = (varName, domSort) :: sctxt
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
                              (checkSubKind kCod (KProper(noRange)))
                | _ ->
                    Error [("Unions can only be taken over index abstractions, not types of kind " + kFun.String, rng)]
            return KProper(noRange)
        }
    | TyTyApp(fn, arg, rng) ->
        check {
            let! kArg = kindSynth sctxt kctxt arg
            let! kFun = kindSynth sctxt kctxt fn
            let! kCod =
                match kFun with
                | KTyFun(kDom, kCod, _) ->
                    check {
                        do! withError ("type " + arg.String + "'s kind " + kArg.String + " is not a subkind of " + kDom.String)
                                      rng
                                      (checkSubKind kArg kDom)
                        return kCod
                    }
                | _ ->
                    Error [("expected " + fn.String + " to be a type function. Instead, it has kind " + kFun.String, rng)]
            return kCod
        }
    | TyIndApp(fn, arg, rng) ->
        check {
            let! sArg = sortCheckAtom sctxt arg rng
            let! kFun = kindSynth sctxt kctxt fn
            let! kRes =
                match kFun with
                | KIndFun(varName, sDom, kCod, _) ->
                    check {
                        do! withError ("index " + arg.String + "'s sort " + sArg.String + " is not a subsort of " + sDom.String)
                                      rng
                                      (checkSubSort sArg sDom)
                        return kCod.subst(arg, varName)
                    }
                | _ ->
                    Error [("Expected " + fn.String + " to be an index abstraction, but instead it has kind " + kFun.String, fn.Range)]
            let! kRes' = applyProofs sctxt kRes rng
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
