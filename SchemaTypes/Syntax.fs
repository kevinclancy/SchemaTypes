module Syntax

open FSharp.Text.Lexing
type Range=Position*Position


type Sort =
    | StString of Range
    | StProp of Range
    | StProof of Index * Range
    | StFun of varName : string * domSort : Sort * codSort : Sort * Range

    with
        member this.SortEquals(other : Sort) =
            match (this,other) with
            | (StString(_),StString(_)) ->
                true
            | (StProp(_), StProp(_)) ->
                true
            | (StProof(ind1,_), StProof(ind2,_)) ->
                ind1.IndexEquals(ind2)
            | (StFun(varName1, domSort1, codSort1, _), StFun(varName2, domSort2, codSort2, _)) ->
                // TODO: we really need alpha renaming here
                (varName1 = varName2) && domSort1.SortEquals(domSort2) && codSort1.SortEquals(codSort2)
            | _ ->
                false

        /// Substitute i for x in this
        member this.subst(i : Index, x : string) =
            match this with
            | StString(_) ->
                this
            | StProp(_) ->
                this
            | StProof(ind, rng) ->
                StProof(ind.substSort(i,x), rng)
            | StFun(varName, _, _, _) when varName = x ->
                this
            | StFun(varName, dom, cod, rng) ->
                StFun(varName, dom.subst(i,x), cod.subst(i,x), rng)
                

and Index =
    | IndStringLit of string * Range
    | IndApp of fn : Index * arg : Index * Range
    | IndVar of varName : string * Range
    | IndTrue of Range

    with
        member this.IndexEquals(other : Index) =
            match (this,other) with
            | (IndStringLit(s1, _), IndStringLit(s2, _)) ->
                s1 = s2
            | (IndApp(fn1,arg1,_), IndApp(fn2,arg2,_)) ->
                (fn1.IndexEquals(fn2) && arg1.IndexEquals(arg2))
            | (IndVar(varName1,_), IndVar(varName2,_)) ->
                varName1 = varName2
            | (IndTrue(_), IndTrue(_)) ->
                true
            | _ ->
                false

        /// Substitute i for x in this
        member this.substSort(i : Index, x : string) : Index =
            match this with
            | IndStringLit(_,_) ->
                this
            | IndApp(fn, arg, rng) ->
                IndApp(fn.substSort(i,x), arg.substSort(i,x), rng)
            | IndVar(varName, _) when varName = x ->
                i
            | IndVar(_,_) ->
                this
            | IndTrue(_) ->
                this

type Ty =
    | TyDict of keyVarName : string * domTy : Ty * Range
    | TyRecord of List<string * Ty> * Range
    | TyStringRef of selfVarName : string * formula : Index * Range
    | TyIndAbs of varName : string * codSort : Sort * domTy : Ty * Range
    | TyTyAbs of varName : string * codTy : Ty * domTy : Ty * Range
    | TyUnion of indTyFun : Ty * Range
    | TyTyApp of fn : Ty * arg : Ty * Range
    | TyIndApp of fn : Ty * arg : Index * Range
    
and Kind =
    | KProper of Range
    | KTyFun of dom : Kind * cod : Kind * Range
    | KIndFun of dom : Sort * cod : Kind * Range

type KindContext = Map<string, Kind>
type SortContext = List<string * Sort>

type AppClassifier =
    | IndToTy
    | TyToTy