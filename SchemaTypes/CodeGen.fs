module CodeGen

open Utils
open Syntax
open Eval
open DecisionProcedures
open MCode
open GenComputation

//let rec merge (a : SortContext) (b : SortContext) =
//    match (a, b) with
//    | ((aname, ast, asat) :: arest, (bname, bst, bsat) :: brest) when bname = aname && ast.SortEquals(bst) ->
//        (aname, ast, Set.union asat bsat) :: merge arest brest
//    | ([], []) ->
//        []
//    | _ ->
//        failwith "tried to merge sort contexts that do not match"

/// augment sort context with decision procedure requirement
//let augment (sctxt : SortContext) (reqCtxt : CanonicalSortContext) : SortContext =
//    let usedPreds (ind : Index) : Set<string> =
//        match ind with
//        | FlatApp(fn, _) ->
//            Set.singleton fn
//        | _ ->
//            Set.empty
//    let usedPreds = Set.unionMany (Set.map usedPreds reqCtxt.proofs)
//    let rec augmentAux (sctxt : SortContext) =
//        match sctxt with
//        | (name, (StFun(_, _, _, _) as stFun)) :: rest when usedPreds.Contains name ->
//            (name, stFun, satellites.Add(DecisionProcedureRequirement reqCtxt)) :: rest
//        | head :: rest ->
//            head :: augmentAux rest
//        | [] ->
//            []
//    augmentAux sctxt

type GenContext = {
    sctxt : SortContext

}

/// Returns a M block asserting that @loc satisfies the type,
/// along with a boolean indicating whether or not the instances satisfying the type are populated 
let rec genCode (sctxt : SortContext) (ty : Ty) : Gen<MCode * bool> =
    assert ty.IsNormalized(sctxt)
    match ty with
    | TyDict(keyVarName, keySort, domTy, rng) ->
        gen {
            let sctxt' = (keyVarName, keySort) :: sctxt
            let! assertBody, isBodyPopulated = genCode sctxt' domTy
            return MBlock [
                MLine <| sprintf "n %s" keyVarName
                MLine <| sprintf "s %s=\"\"" keyVarName
                MLine <| sprintf "f  s %s=$o(@loc@(%s)) q:%s=\"\"  d" keyVarName keyVarName keyVarName
                MBlock [
                    MLine <| sprintf "s loc=$na(@loc@(%s)),level=level+1" keyVarName
                    MLine "d"
                    assertBody
                    MLine <| "s level=level-1,loc=$na(@loc,level)"
                ]
            ], false
        }
    | TyRecord(fields, _) when not (canonicalize sctxt).strings.IsEmpty ->
        let foldField ((assertions, prevPopulated) : List<MCode> * bool) 
                      ((nm,ty) : string * Ty) : Gen<List<MCode> * bool> =
            gen {
                let sctxt' = ("_", StStringLit(nm, noRange)) :: sctxt
                let! assertBody, isBodyPopulated = genCode sctxt' ty
                let fieldAssertion = [
                    MLine <| sprintf "s loc=$na(@loc@(\"%s\")),level=level+1" nm
                    MLine "d"
                    assertBody
                    MLine <| "s level=level-1,loc=$na(@loc,level)"
                ]
                return (List.append fieldAssertion assertions), (prevPopulated || isBodyPopulated)
            }
        gen {
            let! assertions,allPopulated = foldM ([], true) foldField fields
            return (MBlock assertions, allPopulated)
        }
    | TyRecord(fields, _) ->
        let foldField ((assertions, prevPopulated) : List<MCode> * bool) 
                      ((nm,ty) : string * Ty) : Gen<List<MCode> * bool> =
            gen {
                let sctxt' = ("_", StStringLit(nm, noRange)) :: sctxt
                let! assertBody, isBodyPopulated = genCode sctxt' ty
                let fieldAssertion = [
                    MLine <| sprintf "s loc=$na(^%s),level=level+1" nm
                    MLine "d"
                    assertBody
                    MLine <| "s level=level-1"
                ]
                return (List.append fieldAssertion assertions), (prevPopulated || isBodyPopulated)
            }
        gen {
            let! assertions,allPopulated = foldM ([], true) foldField fields
            return (MBlock (MLine "n loc,level" :: MLine "s level=-1" :: assertions), allPopulated)
        }
    | TyStringRef(selfVarName, boundSort, IndTrue(_), _) ->
        gen {
            let canCtxt = canonicalize sctxt 
            let canCtxt' = { 
                canCtxt with 
                  strings = (selfVarName, boundSort) :: canCtxt.strings 
            }
            //// todo: add assertion for bound sort
            return (MBlock [MLine "i 0  w \"skip\""], true)
        }
    | TyStringRef(selfVarName, boundSort, formula, _) ->
        gen {
            let canCtxt = canonicalize sctxt 
            let site = { 
                 sctxt = canCtxt  
                 formulaToDecide = formula
                 selfVar = selfVarName
                 selfSort = boundSort
            }
            let! reqId = addReq site
            //// todo: add assertion for bound sort
            return (MBlockVar reqId, true)
        }
    | TyIndAbs(_, _, _, _)
    | TyTyAbs(_, _, _, _) ->
        failwith "impossible if type is normalized and is proper type"
    | TyUnion(TyIndAbs(varName, domSort, codTy, _) as abs, _) ->
        System.Console.WriteLine("joining " + varName)
        gen {
            let sctxt' = (varName, domSort) :: sctxt
            let! assertBody, isBodyPopulated = genCode sctxt' codTy
            do! 
                match isBodyPopulated with 
                | true -> 
                    addSupplier (canonicalize sctxt')
                | false ->
                    pass
            let! assertBody' =
                match domSort with
                | StFun(_, _, _, _) ->
                    let subProd (code : MCode) 
                                ((i, reqCtxt, optKeys) : int * DecisionSite * Option<List<DecisionProcedureKey>>) : Gen<MCode> =
                        match optKeys with
                        | Some(keys) ->
                            gen {
                                let lookups = String.concat "," (List.map (fun (x : DecisionProcedureKey) -> x.String) keys.Tail)
                                let headStr = 
                                    match keys.Head with
                                    | LiteralKey(s) ->
                                        s
                                    | ArgumentKey(_) ->
                                        failwith "todo: enforce outer-level record type"
                                let ln = MBlock [
                                    MLine <| sprintf "i '$d(^%s(%s)) w \"Validation Error: Expected \"_$na(^%s(%s))_\" to be populated when validating \"_loc,!"
                                                     headStr 
                                                     lookups 
                                                     headStr 
                                                     lookups
                                ]
                                return code.subst(i, ln)
                            }
                        | None ->
                            error <| "Could not find decision procedure for: " + reqCtxt.String
                    System.Console.WriteLine("varName:  " + varName)
                    gen {
                        let! allSuppliers = getSuppliers
                        let! reqs, suppliers = removePred varName
                        // for each requirement site, try instantiating with all suppliers
                        let instantiations = Set.map (fun (i, reqCtxt) -> (i, reqCtxt, List.tryPick (instantiate2 reqCtxt) (Set.toList allSuppliers))) reqs
                        
                        // requirements should actually be a map probably
                        let! res = foldM assertBody subProd (Set.toList instantiations)
                        return res
                    }
                | _ ->
                    gen {
                        return assertBody
                    }

            return (assertBody', false)
        }
    | TyUnion(_,_)
    | TyTyApp(_, _, _)
    | TyIndApp(_, _, _)
    | TyVar(_, _)
    | TyLet(_,_,_,_) ->
        failwith "impossible if type is normalized and is proper type"

        //TODO: I need to create some sort of unique identifier for the decision procedure
        //should I use a computation to do this? create some sort of "code-gen" computation?