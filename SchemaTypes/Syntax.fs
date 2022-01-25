module Syntax

open FSharp.Text.Lexing
type Range=Position*Position


type Sort =
    | StString of Range
    | StStringLit of string * Range
    | StProp of Range
    | StProof of Index * Range
    | StFun of varName : string * domSort : Sort * codSort : Sort * Range

    with
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
                StProof(ind.substSort(i,x), rng)
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
            | _ ->
                failwith "todo"
        
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
    | TyIndAbs of varName : string * codSort : Sort * domTy : Ty * Range
    | TyTyAbs of varName : string * codKind : Kind * domTy : Ty * Range
    | TyUnion of indTyFun : Ty * Range
    | TyTyApp of fn : Ty * arg : Ty * Range
    | TyIndApp of fn : Ty * arg : Index * Range
    
    with
        
        member this.Range =
            match this with
            | TyDict(_,_,_,rng)
            | TyRecord(_,rng)
            | TyStringRef(_,_,_,rng)
            | TyIndAbs(_,_,_,rng)
            | TyTyAbs(_,_,_,rng)
            | TyUnion(_,rng)
            | TyTyApp(_,_,rng)
            | TyIndApp(_,_,rng) ->
                rng

and Kind =
    | KProper of Range
    | KProperPopulated of Range
    | KTyFun of dom : Kind * cod : Kind * Range
    | KIndFun of dom : Sort * cod : Kind * Range

type DecisionProcedureKey =
    /// We must use the string denoted by the variable varName at this position
    | ArgumentKey of varName : string
    /// we must use the string lit as the key at this position
    | LiteralKey of lit : string

type DecisionProcedure = {
    /// names of string variables that this decision procedure abstracts over
    vars : Set<string>

    // set of proofs we are deciding
    proofs : Set<Index>

    // the sequence of lookups needed to decide the set of proofs
    keys : List<DecisionProcedureKey>
}

type Satellite =
    /// all of the information necessary to create a decision procedure for a predicate in context
    | DecisionProcedure of DecisionProcedure
    /// we require a decision procedure for this predicate before the variable this satellite is attached to goes out of scope
    | DecisionProcedureRequirement of predicateName : string

type KindContext = Map<string, Kind>

type SortContext = List<string * Sort * Set<Satellite>>

type CanonicalSortContext = {
    // ------- Left segment of context -------

    /// List of context entries bound to StString and StStringLit sorts
    // to simplify, all strings are physical. I'm not sure if non-physical strings are useful.
    // we can just normalize before running the validation generator
    strings : List<string * Sort>

    /// Props - it's not clear why we would have props in our context
    props : Set<string>

    // ------- Middle segment of context -------
    
    /// Bindings with function sorts
    predicates : List<string * Sort * Set<Satellite>>

    // ------- Right segment of context -------
 
    /// Set of propositions that our context contains proofs of
    // invariant: these all map the FlatApp active pattern
    proofs : Set<Index>
}

    with
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

