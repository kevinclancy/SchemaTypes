module CodeGen

open Utils
open Syntax
open Eval
open DecisionProcedures
open MCode

let rec merge (a : SortContext) (b : SortContext) =
    match (a, b) with
    | ((aname, ast, asat) :: arest, (bname, bst, bsat) :: brest) when bname = aname && ast.SortEquals(bst) ->
        (aname, ast, Set.union asat bsat) :: merge arest brest
    | ([], []) ->
        []
    | _ ->
        failwith "tried to merge sort contexts that do not match"

/// augment sort context with decision procedure requirement
let augment (sctxt : SortContext) (reqCtxt : CanonicalSortContext) : SortContext =
    let usedPreds (ind : Index) : Set<string> =
        match ind with
        | FlatApp(fn, _) ->
            Set.singleton fn
        | _ ->
            Set.empty
    let usedPreds = Set.unionMany (Set.map usedPreds reqCtxt.proofs)
    let rec augmentAux (sctxt : SortContext) =
        match sctxt with
        | (name, (StFun(_, _, _, _) as stFun), satellites) :: rest when usedPreds.Contains name ->
            (name, stFun, satellites.Add(DecisionProcedureRequirement reqCtxt)) :: rest
        | head :: rest ->
            head :: augmentAux rest
        | [] ->
            []
    augmentAux sctxt

type GenContext = {
    sctxt : SortContext

}

let rec genCode (sctxt : SortContext) (ty : Ty) : MCode =
    assert ty.IsNormalized(sctxt)
    match ty with
    | TyDict(keyVarName, keySort, domTy, rng) ->
        let sctxt' = (keyVarName, keySort, Set.empty) :: sctxt
        let sctxt'', assertBody = gen sctxt' domTy
        let assertion = MBlock [
            MLine <| sprintf "n %s" keyVarName
            MLine <| sprintf "f  s %s=$o(@loc@(%s)) q:%s=\"\" d" keyVarName keyVarName keyVarName
            MBlock [
                MLine <| sprintf "s loc=$na(@loc@(%s)),level=level+1" keyVarName
                MLine "d"
                assertBody
                MLine <| "s level=level-1,loc=$na(@loc,level)"
            ]
        ]
        sctxt'', assertion
    | TyRecord(fields, _) ->
        let foldField ((sctxt, assertions) : SortContext * List<MCode>) 
                      ((nm,ty) : string * Ty) : SortContext * List<MCode> =
            let sctxt' = ("_", StStringLit(nm, noRange), Set.empty) :: sctxt
            let sctxt'', assertBody = gen sctxt' ty
            let fieldAssertion = MBlock [
                MLine <| sprintf "s loc=$na(@loc@(%s)),level=level+1" nm
                MLine "d"
                assertBody
                MLine <| "s level=level-1,loc=$na(@loc,level)"
            ]
            sctxt'', (fieldAssertion :: assertions)
        let sctxt',assertions = List.fold foldField (sctxt, []) fields
        sctxt', MBlock assertions
    | TyUnion(TyIndAbs(_, _, _, _) as abs, _) ->
        gen sctxt abs
    | TyUnion(_,_) ->
        failwith "impossible if type is normalized and well kinded"
    | TyStringRef(selfVarName, boundSort, formula, _) ->
        failwith "todo"
        //// todo: make assertion for bound sort
        let canCtxt = canonicalize sctxt 
        let canCtxt' = { 
            canCtxt with 
              strings = (selfVarName, boundSort) :: canCtxt.strings 
              proofs = canCtxt.proofs.Add(formula)
        }
        //TODO: I need to create some sort of unique identifier for the decision procedure
        //should I use a computation to do this? create some sort of "code-gen" computation?