/// Compilation of the surface language to the core language.
///
/// The two languages only differ at the index level, where this replaces n-ary predicates with
/// curried functions.
module Surface.Compile

open Utils

module S = Surface.Syntax
module C = Core.Syntax

let compileAtom (atom : S.Atom) : C.Index =
    match atom with
    | S.AtomVar(varName) ->
        C.IndVar(varName, noRange)
    | S.AtomLit(str) ->
        C.IndStringLit(str, noRange)

/// P(a1, ..., an) becomes (((P a1) ...) an)
let compilePredApp (app : S.PredApp) : C.Index =
    List.fold (fun fn arg -> C.IndApp(fn, compileAtom arg, noRange)) (C.IndVar(app.pred, noRange)) app.args

let compileFormula (formula : S.Formula) : C.Index =
    match formula with
    | S.FmTrue ->
        C.IndTrue(noRange)
    | S.FmApp(app) ->
        compilePredApp app

let compileStrSort (strSort : S.StrSort) (rng : S.Range) : C.Sort =
    match strSort with
    | S.SsString ->
        C.StString(rng)
    | S.SsLit(lit) ->
        C.StStringLit(lit, rng)

/// (x1 : s1, ..., xn : sn | p1, ..., pm) -> prop becomes
/// (x1 : s1) -> ... -> (xn : sn) -> prf p1 -> ... -> prf pm -> prop
let compilePredSig (predSig : S.PredSig) (rng : S.Range) : C.Sort =
    let addProof (proof : S.PredApp) (cod : C.Sort) =
        C.StFun("_", C.StProof(compilePredApp proof, rng), cod, rng)
    let addString ((varName, strSort) : string * S.StrSort) (cod : C.Sort) =
        C.StFun(varName, compileStrSort strSort rng, cod, rng)
    List.foldBack addString predSig.strings (List.foldBack addProof predSig.proofs (C.StProp(rng)))

let compileSort (sort : S.Sort) : C.Sort =
    match sort with
    | S.StStr(strSort, rng) ->
        compileStrSort strSort rng
    | S.StProof(formula, rng) ->
        C.StProof(compileFormula formula, rng)
    | S.StPred(predSig, rng) ->
        compilePredSig predSig rng

let rec compileKind (kind : S.Kind) : C.Kind =
    match kind with
    | S.KProper(rng) ->
        C.KProper(rng)
    | S.KProperPopulated(rng) ->
        C.KProperPopulated(rng)
    | S.KTyFun(dom, cod, rng) ->
        C.KTyFun(compileKind dom, compileKind cod, rng)
    | S.KIndFun(varName, dom, cod, rng) ->
        C.KIndFun(varName, compileSort dom, compileKind cod, rng)

let rec compileTy (ty : S.Ty) : C.Ty =
    match ty with
    | S.TyDict(keyVarName, keySort, domTy, rng) ->
        C.TyDict(keyVarName, compileStrSort keySort rng, compileTy domTy, rng)
    | S.TyRecord(fields, rng) ->
        C.TyRecord(List.map (fun (name, fieldTy) -> (name, compileTy fieldTy)) fields, rng)
    | S.TyStringRef(selfVarName, boundSort, formula, rng) ->
        C.TyStringRef(selfVarName, compileStrSort boundSort rng, compileFormula formula, rng)
    | S.TyIndAbs(varName, domSort, codTy, rng) ->
        C.TyIndAbs(varName, compileSort domSort, compileTy codTy, rng)
    | S.TyTyAbs(varName, domKind, codTy, rng) ->
        C.TyTyAbs(varName, compileKind domKind, compileTy codTy, rng)
    | S.TyUnion(indTyFun, rng) ->
        C.TyUnion(compileTy indTyFun, rng)
    | S.TyTyApp(fn, arg, rng) ->
        C.TyTyApp(compileTy fn, compileTy arg, rng)
    | S.TyIndApp(fn, arg, rng) ->
        C.TyIndApp(compileTy fn, compileAtom arg, rng)
    | S.TyVar(name, rng) ->
        C.TyVar(name, rng)
    | S.TyLet(name, rhsTy, bodyTy, rng) ->
        C.TyLet(name, compileTy rhsTy, compileTy bodyTy, rng)
