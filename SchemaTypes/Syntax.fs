module Syntax

open FSharp.Text.Lexing
type Range=Position*Position
open Utils

let freshVar (freeVars : Set<string>) (seed : string) : string =
    let seedStr, seedInt = 
        match Seq.tryFindIndex System.Char.IsDigit seed with
        | Some n ->
            (seed.Substring(0,n), System.Int32.Parse(seed.Substring(n)))
        | None ->
            (seed, 0)
    let rec getSuffix (seedStr : string) (candidate : int) : int =
        match freeVars.Contains (seedStr + candidate.ToString()) with
        | true ->
            getSuffix seedStr (candidate + 1)
        | false ->
            candidate
    seedStr + (getSuffix seedStr seedInt).ToString()

type Sort =
    | StString of Range
    | StStringLit of string * Range
    | StProp of Range
    | StProof of Index * Range
    | StFun of varName : string * domSort : Sort * codSort : Sort * Range

    with
        member this.String =
            match this with
            | StString(_) ->
                "str"
            | StStringLit(s, _) ->
                s
            | StProp(_) ->
                "prop"
            | StProof(ind, _) ->
                "prf " + ind.String
            | StFun(varName, domSort, codSort, _) ->
                match varName with
                | "_" ->
                    domSort.String + " -> " + codSort.String
                | _ ->
                    "(" + varName + " : " + domSort.String + ")" + " -> " + codSort.String
                
        member this.Range =
            match this with
            | StString(rng)
            | StStringLit(_,rng)
            | StProp(rng)
            | StProof(_,rng)
            | StFun(_,_,_,rng) ->
                rng
                
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
            | StString(_) 
            | StStringLit(_) 
            | StProp(_) ->
                this
            | StProof(ind, rng) ->
                StProof(ind.subst(i,x), rng)
            | StFun(varName, _, _, _) when varName = x ->
                this
            | StFun(varName, dom, cod, rng) ->
                StFun(varName, dom.subst(i,x), cod.subst(i,x), rng)
        
        /// Substitute st for x in this
        member this.substSort(st : Sort, x : string) =
            match this with
            | StString(_) 
            | StStringLit(_) 
            | StProp(_)
            | StProof(_, _) ->
                this
            | StFun(varName, _, _, _) when varName = x ->
                this
            | StFun(varName, dom, cod, rng) ->
                StFun(varName, dom.substSort(st,x), cod.substSort(st,x), rng)
 
        member this.freeVars =
            match this with
            | StString(_)
            | StStringLit(_)
            | StProp(_) ->
                Set.empty
            | StProof(ind, _) ->
                ind.freeVars
            | StFun(varName, domSort, codSort, _) ->
                Set.union domSort.freeVars (codSort.freeVars.Remove varName)

and Index =
    | IndStringLit of string * Range
    | IndApp of fn : Index * arg : Index * Range
    | IndVar of varName : string * Range
    | IndTrue of Range

    with
        member this.String : string =
            match this with
            | IndStringLit(str, _) ->
                "\"" + str + "\""
            | IndApp(fn, arg, _) ->
                "(" + fn.String + " " + arg.String + ")"
            | IndVar(varName, _) ->
                varName
            | IndTrue(_) ->
                "true"

        member this.Range =
            match this with
            | IndStringLit(_, rng)
            | IndApp(_,_,rng) 
            | IndVar(_,rng)
            | IndTrue(rng) ->
                rng

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
        member this.subst(i : Index, x : string) : Index =
            match this with
            | IndStringLit(_,_) ->
                this
            | IndApp(fn, arg, rng) ->
                IndApp(fn.subst(i,x), arg.subst(i,x), rng)
            | IndVar(varName, _) when varName = x ->
                i
            | IndVar(_,_) ->
                this
            | IndTrue(_) ->
                this

        member this.freeVars : Set<string> =
            match this with
            | IndStringLit(_,_) ->
                Set.empty
            | IndApp(fn, arg, _) ->
                Set.union fn.freeVars arg.freeVars
            | IndVar(varName, _) ->
                Set.singleton varName
            | IndTrue(_) ->
                Set.empty


type Ty =
    | TyDict of keyVarName : string * keySort : Sort * domTy : Ty * Range
    | TyRecord of List<string * Ty> * Range
    | TyStringRef of selfVarName : string * boundSort : Sort * formula : Index * Range
    | TyIndAbs of varName : string * domSort : Sort * codTy : Ty * Range
    | TyTyAbs of varName : string * domKind : Kind * codTy : Ty * Range
    | TyUnion of indTyFun : Ty * Range
    | TyTyApp of fn : Ty * arg : Ty * Range
    | TyIndApp of fn : Ty * arg : Index * Range
    | TyVar of name : string * Range
    | TyLet of name : string * rhsTy : Ty * bodyTy : Ty * Range

    with

        member this.freeIndVars : Set<string> =
            match this with
            | TyDict(keyVarName, keySort, domTy, _) ->
                Set.union keySort.freeVars (Set.remove keyVarName domTy.freeIndVars)
            | TyRecord(fields, _) ->
                Set.unionMany (List.map (fun (_, ty : Ty) -> ty.freeIndVars) fields) 
            | TyStringRef(selfVarName, boundSort, formula, _) ->
                Set.union boundSort.freeVars (Set.remove selfVarName formula.freeVars) 
            | TyIndAbs(varName, domSort, codTy, _) ->
                Set.union domSort.freeVars (Set.remove varName codTy.freeIndVars)
            | TyTyAbs(varName, domKind, codTy, _) ->
                Set.union domKind.freeIndVars codTy.freeIndVars
            | TyUnion(indTyFun, _) ->
                indTyFun.freeIndVars
            | TyTyApp(fn, arg, _) ->
                Set.union fn.freeIndVars arg.freeIndVars
            | TyIndApp(fn, arg, _) -> 
                Set.union fn.freeIndVars arg.freeVars
            | TyVar(name, _) ->
                Set.empty
            | TyLet(name, rhsTy, bodyTy, _) ->
                Set.union rhsTy.freeIndVars bodyTy.freeIndVars

        member this.freeTyVars : Set<string> =
            match this with
            | TyDict(keyVarName, keySort, domTy, _) ->
                domTy.freeIndVars
            | TyRecord(fields, _) ->
                Set.unionMany (List.map (fun (_, ty : Ty) -> ty.freeTyVars) fields) 
            | TyStringRef(selfVarName, boundSort, formula, _) ->
                Set.empty 
            | TyIndAbs(varName, domSort, codTy, _) ->
                codTy.freeTyVars
            | TyTyAbs(varName, domKind, codTy, _) ->
                Set.remove varName codTy.freeIndVars
            | TyUnion(indTyFun, _) ->
                indTyFun.freeIndVars
            | TyTyApp(fn, arg, _) ->
                Set.union fn.freeIndVars arg.freeIndVars
            | TyIndApp(fn, arg, _) -> 
                Set.union fn.freeIndVars arg.freeVars
            | TyVar(name, _) ->
                Set.singleton name
            | TyLet(name, rhsTy, bodyTy, _) ->
                Set.union rhsTy.freeTyVars (Set.remove name bodyTy.freeTyVars)           

        member this.String =
            match this with
            | TyDict(keyVarName, keySort, domTy, _) ->
                "{ [" + keyVarName + " : " + keySort.String + "] : " + domTy.String + " }"
            | TyRecord(fields, _) ->
                let fieldToString ((name, ty) : string * Ty) =
                    name + " : " + ty.String
                "{ " + (String.concat ", " <| List.map fieldToString fields) + " }"
            | TyStringRef(selfVarName, boundSort, formula, _) ->
                "{ " + selfVarName + " | " + formula.String + " }"
            | TyIndAbs(varName, domSort, codTy, _) ->
                "(" + varName + ":" + domSort.String + ") => " + codTy.String
            | TyTyAbs(varName, domKind, codTy, _) ->
                "(" + varName + "::" + domKind.String + ") => " + codTy.String
            | TyUnion(indTyFun, _) ->
                "union " + indTyFun.String
            | TyTyApp(fn, arg, _) ->
                "(" + fn.String + " !" + arg.String + ")"
            | TyIndApp(fn, arg, _) ->
                "(" + fn.String + " " + arg.String + ")"
            | TyVar(name, _) ->
                name
            | TyLet(boundVarName, rhsTy, bodyTy, _) ->
                "let " + boundVarName + " = " + rhsTy.String + "in\n" + bodyTy.String

        member this.substInd(varName : string, ind : Index) : Ty =
            match this with
            | TyDict(keyVarName, keySort, domTy, rng) when keyVarName <> varName ->
                let keyVarName' = freshVar (Set.union domTy.freeIndVars ind.freeVars) keyVarName
                let domTy' = domTy.substInd(keyVarName, IndVar(keyVarName', noRange))
                TyDict(keyVarName', keySort.subst(ind, varName), domTy'.substInd(varName, ind), rng)
            | TyDict(_, _, _, _) ->
                this
            | TyRecord(fields, rng) ->
                TyRecord(List.map (fun (x : string, T : Ty) -> (x, T.substInd(varName, ind))) fields, rng)
            | TyStringRef(selfVarName, boundSort, formula, rng) when selfVarName <> varName ->
                let selfVarName' = freshVar (Set.union formula.freeVars ind.freeVars) selfVarName
                let formula' = formula.subst(IndVar(selfVarName', noRange), selfVarName)
                TyStringRef(selfVarName', boundSort.subst(ind, varName), formula'.subst(ind, varName), rng)
            | TyStringRef(_, _, _, _) ->
                this
            | TyIndAbs(absVarName, domSort, codTy, rng) when varName <> absVarName ->
                let absVarName' = freshVar (Set.union ind.freeVars codTy.freeIndVars) absVarName
                let codTy' = codTy.substInd(absVarName, IndVar(absVarName', noRange))
                TyIndAbs(absVarName', domSort.subst(ind, varName), codTy'.substInd(varName, ind), rng)
            | TyIndAbs(absVarName, domSort, codTy, rng) ->
                TyIndAbs(absVarName, domSort.subst(ind, varName), codTy, rng)
            | TyTyAbs(absVarName, domKind, codTy, rng) ->
                TyTyAbs(absVarName, domKind.subst(ind, varName), codTy.substInd(varName, ind), rng)
            | TyUnion(indTyFun, rng) ->
                TyUnion(indTyFun.substInd(varName, ind), rng)
            | TyTyApp(fn, arg, rng) ->
                TyTyApp(fn.substInd(varName, ind), arg.substInd(varName, ind), rng)
            | TyIndApp(fn, arg, rng) ->
                TyIndApp(fn.substInd(varName, ind), arg.subst(ind, varName), rng)
            | TyVar(_, _) ->
                this
            | TyLet(boundVarName, rhsTy, bodyTy, rng) ->
                TyLet(boundVarName, rhsTy.substInd(varName, ind), bodyTy.substInd(varName, ind), rng)

        member this.substTy(varName : string, other : Ty) : Ty =
            match this with
            | TyDict(keyVarName, keySort, domTy, rng) ->
                TyDict(keyVarName, keySort, domTy.substTy(varName, other), rng)
            | TyRecord(fields, rng) ->
                TyRecord(List.map (fun (name : string, ty : Ty) -> (name, ty.substTy(varName, other))) fields, rng)
            | TyStringRef(_, _, _, _) ->
                this
            | TyIndAbs(absVar, domSort, codTy, rng) ->
                TyIndAbs(absVar, domSort, codTy.substTy(varName, other), rng)
            | TyTyAbs(absVar, domKind, codTy, rng) when absVar <> varName ->
                TyTyAbs(absVar, domKind, codTy.substTy(varName, other), rng)
            | TyTyAbs(_, _, _, _) ->
                this
            | TyUnion(indTyFun, rng) ->
                TyUnion(indTyFun.substTy(varName, other), rng)
            | TyTyApp(fn, arg, rng) ->
                TyTyApp(fn.substTy(varName, other), arg.substTy(varName, other), rng)
            | TyIndApp(fn, arg, rng) ->
                TyIndApp(fn.substTy(varName, other), arg, rng)
            | TyVar(name, varRng) when name = varName ->
                other // TODO: maybe replace all ranges in other with varRng
            | TyVar(_, _) ->
                this
            | TyLet(boundVar, rhsTy, bodyTy, rng) when boundVar <> varName ->
                TyLet(boundVar, rhsTy.substTy(varName, other), bodyTy.substTy(varName, other), rng)
            | TyLet(boundVar, rhsTy, bodyTy, rng) ->
                TyLet(boundVar, rhsTy.substTy(varName, other), bodyTy, rng)

        member this.Range =
            match this with
            | TyDict(_,_,_,rng)
            | TyRecord(_,rng)
            | TyStringRef(_,_,_,rng)
            | TyIndAbs(_,_,_,rng)
            | TyTyAbs(_,_,_,rng)
            | TyUnion(_,rng)
            | TyTyApp(_,_,rng)
            | TyIndApp(_,_,rng) 
            | TyVar(_,rng)
            | TyLet(_,_,_,rng) ->
                rng

and Kind =
    | KProper of Range
    | KProperPopulated of Range
    | KTyFun of dom : Kind * cod : Kind * Range
    | KIndFun of varName : string * dom : Sort * cod : Kind * Range

    with
        member this.freeIndVars =
            match this with
            | KProper(_)
            | KProperPopulated(_) ->
                Set.empty
            | KTyFun(kDom, kCod, _) ->
                Set.union kDom.freeIndVars kCod.freeIndVars
            | KIndFun(varName, sDom, kCod, _) ->
                Set.union sDom.freeVars (Set.remove varName kCod.freeIndVars)

        member this.String =
            match this with
            | KProper(_) ->
                "*"
            | KProperPopulated(_) ->
                "**"
            | KTyFun(dom, cod, _) ->
                dom.String + " -> " + cod.String
            | KIndFun(varName, dom, cod, _) ->
                "(" + varName + " : " + dom.String + ") -> " + cod.String
            
        member this.subst(i : Index, x : string) =
            match this with
            | KProper(_)
            | KProperPopulated(_) ->
                this
            | KTyFun(kDom, kCod, rng) ->
                KTyFun(kDom.subst(i,x), kCod.subst(i,x), rng)
            | KIndFun(varName, _, _, _) when varName = x ->
                this
            | KIndFun(varName, sDom, kCod, rng) ->
                KIndFun(varName, sDom.subst(i,x), kCod.subst(i,x), rng)

        member this.Range =
            match this with
            | KProper(rng)
            | KProperPopulated(rng)
            | KTyFun(_,_,rng)
            | KIndFun(_,_,_,rng) ->
                rng
                

type DecisionProcedureKey =
    /// We must use the string denoted by the variable varName at this position
    | ArgumentKey of varName : string
    /// we must use the string lit as the key at this position
    | LiteralKey of lit : string

    with

        member this.String =
            match this with
            | ArgumentKey(varName) ->
                varName
            | LiteralKey(lit) ->
                "\"" + lit + "\""
                 
type DecisionProcedure = {
    /// names of string variables that this decision procedure abstracts over
    vars : Set<string>

    // set of proofs we are deciding
    proofs : Set<Index>

    // the sequence of lookups needed to decide the set of proofs
    keys : List<DecisionProcedureKey>
}

type KindContext = Map<string, Kind>

type SortContext = List<string * Sort>

and Satellite =
    /// all of the information necessary to create a decision procedure for a predicate in context
    | DecisionProcedure of CanonicalSortContext
    /// we require a decision procedure for this predicate before the variable this satellite is attached to goes out of scope
    | DecisionProcedureRequirement of CanonicalSortContext

and CanonicalSortContext = {
    // ------- Left segment of context -------

    /// List of context entries bound to StString and StStringLit sorts
    // to simplify, all strings are physical. I'm not sure if non-physical strings are useful.
    // we can just normalize before running the validation generator
    strings : List<string * Sort>

    /// Props - it's not clear why we would have props in our context
    props : Set<string>

    // ------- Middle segment of context -------
    
    /// Bindings with function sorts
    //predicates : List<string * Sort * Set<Satellite>>
    predicates : List<string * Sort>

    // ------- Right segment of context -------
 
    /// Set of propositions that our context contains proofs of
    // invariant: these all map the FlatApp active pattern
    proofs : Set<Index>
}

    with
        member this.String =
            let stringsStr = String.concat " , " <| List.map (fun (x,st : Sort) -> sprintf "%s : %s" x st.String) this.strings
            let predsStr = String.concat " , " <| List.map (fun (x,st : Sort) -> sprintf "%s : %s" x st.String) this.predicates
            sprintf "strings: %s\npredicates: %s\nproofs: %s" stringsStr predsStr this.StringProofs
               
        member this.StringProofs =
            String.concat "," (Seq.map (fun (ind : Index) -> ind.String) 
                              (Set.toSeq this.proofs))

        static member empty : CanonicalSortContext =
            { 
                strings = []
                props = Set.empty
                predicates = [] 
                proofs = Set.empty
            }



// to match proposition-in-contexts (one is a template, the other is a concrete proposition-in-context):
//   Convert template to canonical form, where:
//     - all variables bound to propositions have been moved to the right end of the context
//     - irrelevant bindings (those that don't affect the proposition directly or transitively) have been removed
//     - template is paired with a left-to-right list of lookups, including its own variables and also literal string lookups
//
//   We also need a matching procedure:
//     - assigns concrete string variables to template string variables  

type DecisionTemplate = {

    /// we can decide any of these propositions if we assume all others
    propSet : Set<Index>

    /// a context containing all variables as predicates occuring in the propSet
    args : SortContext

}

type AppClassifier =
    | IndToTy
    | TyToTy

