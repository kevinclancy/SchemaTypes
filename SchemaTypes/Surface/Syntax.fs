/// The surface language: the language that schemas are written in.
///
/// It differs from the core language (Core.Syntax) at the index level. Core index functions are
/// curried, so a predicate application is a tree of one-argument applications, and proofs may be
/// interleaved with strings in a predicate's sort. Surface predicates are n-ary instead: a predicate
/// is always applied to all of its string arguments at once, and its sort lists its string formals
/// and the proofs it requires in two separate sections.
///
/// The type level is the same as in the core language: index-to-type and type-to-type functions
/// take one argument at a time.
module Surface.Syntax

open FSharp.Text.Lexing
type Range=Position*Position
open Utils

/// An atomic index: a variable or a string literal.
///
/// Atoms are the only indices that can be passed as arguments. An argument of a predicate is always
/// a string. An argument of an index-to-type function may also be a variable naming a predicate.
type Atom =
    | AtomVar of varName : string
    | AtomLit of string

    with
        member this.String : string =
            match this with
            | AtomVar(varName) ->
                varName
            | AtomLit(str) ->
                "\"" + str + "\""

        member this.freeVars : Set<string> =
            match this with
            | AtomVar(varName) ->
                Set.singleton varName
            | AtomLit(_) ->
                Set.empty

        /// Substitute a for x in this
        member this.subst(a : Atom, x : string) : Atom =
            match this with
            | AtomVar(varName) when varName = x ->
                a
            | _ ->
                this

/// A predicate applied to all of its string arguments.
///
/// The predicate's proof arguments are not written. Proofs are irrelevant, so it is enough to know
/// that the sort context contains them.
type PredApp =
    {
        /// name of the predicate variable
        pred : string

        /// the string section of the argument list
        args : List<Atom>
    }

    with
        member this.String : string =
            this.pred + "(" + (String.concat ", " <| List.map (fun (a : Atom) -> a.String) this.args) + ")"

        member this.freeVars : Set<string> =
            Set.add this.pred (Set.unionMany <| List.map (fun (a : Atom) -> a.freeVars) this.args)

        /// Substitute a for x in this
        member this.subst(a : Atom, x : string) : PredApp =
            let pred' =
                match a with
                | AtomVar(varName) when this.pred = x ->
                    varName
                | _ ->
                    // a string literal is never substituted for a predicate in a well-sorted index
                    this.pred
            { pred = pred' ; args = List.map (fun (arg : Atom) -> arg.subst(a, x)) this.args }

        /// Simultaneously substitute atoms for the string variables in the domain of p
        member this.substStrings(p : Map<string, Atom>) : PredApp =
            let substArg (arg : Atom) =
                match arg with
                | AtomVar(varName) when p.ContainsKey varName ->
                    p.[varName]
                | _ ->
                    arg
            { this with args = List.map substArg this.args }

/// An index of sort prop
type Formula =
    | FmTrue
    | FmApp of PredApp

    with
        member this.String : string =
            match this with
            | FmTrue ->
                "true"
            | FmApp(app) ->
                app.String

        member this.freeVars : Set<string> =
            match this with
            | FmTrue ->
                Set.empty
            | FmApp(app) ->
                app.freeVars

        /// Substitute a for x in this
        member this.subst(a : Atom, x : string) : Formula =
            match this with
            | FmTrue ->
                this
            | FmApp(app) ->
                FmApp(app.subst(a, x))

/// A sort that classifies strings
type StrSort =
    /// contains all strings
    | SsString
    /// contains only the string lit
    | SsLit of lit : string

    with
        member this.String : string =
            match this with
            | SsString ->
                "str"
            | SsLit(lit) ->
                "\"" + lit + "\""

/// Returns one fresh variable name per seed. The names are distinct and none of them is in *avoid*.
let freshVars (avoid : Set<string>) (seeds : List<string>) : List<string> =
    let pick ((taken, names) : Set<string> * List<string>) (seed : string) =
        let name = freshVar taken seed
        (taken.Add name, name :: names)
    List.rev << snd <| List.fold pick (avoid, []) seeds

/// The signature of an n-ary predicate. Its formals are kept in two sections.
type PredSig =
    {
        /// String section: the names and sorts of the predicate's string arguments, in order.
        strings : List<string * StrSort>

        /// Proof section: propositions that must have proofs in context wherever the predicate is
        /// applied. They may mention the formals of the string section, as well as variables bound
        /// outside of the signature.
        proofs : List<PredApp>
    }

    with
        member this.String : string =
            let stringsStr = String.concat ", " <| List.map (fun (x, st : StrSort) -> x + " : " + st.String) this.strings
            let proofsStr =
                match this.proofs with
                | [] ->
                    ""
                | _ ->
                    " | " + (String.concat ", " <| List.map (fun (p : PredApp) -> p.String) this.proofs)
            "(" + stringsStr + proofsStr + ")"

        member this.formalNames : List<string> =
            List.map fst this.strings

        member this.freeVars : Set<string> =
            Set.difference (Set.unionMany <| List.map (fun (p : PredApp) -> p.freeVars) this.proofs)
                           (Set.ofList this.formalNames)

        /// The propositions that must have proofs in context for the predicate to be applied to *args*
        member this.instantiate(args : List<Atom>) : List<PredApp> =
            let p = Map.ofList (List.zip this.formalNames args)
            List.map (fun (proof : PredApp) -> proof.substStrings p) this.proofs

        /// Renames the string formals whose names are in *avoid*
        member this.renameFormals(avoid : Set<string>) : PredSig =
            match List.exists avoid.Contains this.formalNames with
            | false ->
                this
            | true ->
                let taken = Set.unionMany [avoid ; this.freeVars ; Set.ofList this.formalNames]
                let formalNames' = freshVars taken this.formalNames
                {
                    strings = List.map2 (fun name' (_, st) -> (name', st)) formalNames' this.strings
                    proofs = this.instantiate(List.map AtomVar formalNames')
                }

        /// Substitute a for x in this
        member this.subst(a : Atom, x : string) : PredSig =
            match List.contains x this.formalNames with
            | true ->
                this
            | false ->
                let this' = this.renameFormals(a.freeVars)
                { this' with proofs = List.map (fun (p : PredApp) -> p.subst(a, x)) this'.proofs }

/// Sorts classify the index variables that we can bind
type Sort =
    | StStr of StrSort * Range
    | StProof of Formula * Range
    | StPred of PredSig * Range

    with
        member this.String : string =
            match this with
            | StStr(strSort, _) ->
                strSort.String
            | StProof(formula, _) ->
                "prf " + formula.String
            | StPred(predSig, _) ->
                "pred " + predSig.String

        member this.Range : Range =
            match this with
            | StStr(_, rng)
            | StProof(_, rng)
            | StPred(_, rng) ->
                rng

        member this.freeVars : Set<string> =
            match this with
            | StStr(_, _) ->
                Set.empty
            | StProof(formula, _) ->
                formula.freeVars
            | StPred(predSig, _) ->
                predSig.freeVars

        /// Substitute a for x in this
        member this.subst(a : Atom, x : string) : Sort =
            match this with
            | StStr(_, _) ->
                this
            | StProof(formula, rng) ->
                StProof(formula.subst(a, x), rng)
            | StPred(predSig, rng) ->
                StPred(predSig.subst(a, x), rng)

type Kind =
    | KProper of Range
    | KProperPopulated of Range
    | KTyFun of dom : Kind * cod : Kind * Range
    | KIndFun of varName : string * dom : Sort * cod : Kind * Range

    with
        member this.freeIndVars : Set<string> =
            match this with
            | KProper(_)
            | KProperPopulated(_) ->
                Set.empty
            | KTyFun(kDom, kCod, _) ->
                Set.union kDom.freeIndVars kCod.freeIndVars
            | KIndFun(varName, sDom, kCod, _) ->
                Set.union sDom.freeVars (Set.remove varName kCod.freeIndVars)

        member this.String : string =
            match this with
            | KProper(_) ->
                "*"
            | KProperPopulated(_) ->
                "**"
            | KTyFun(dom, cod, _) ->
                dom.String + " -> " + cod.String
            | KIndFun(varName, dom, cod, _) ->
                "(" + varName + " : " + dom.String + ") -> " + cod.String

        /// Substitute a for x in this
        member this.subst(a : Atom, x : string) : Kind =
            match this with
            | KProper(_)
            | KProperPopulated(_) ->
                this
            | KTyFun(kDom, kCod, rng) ->
                KTyFun(kDom.subst(a,x), kCod.subst(a,x), rng)
            | KIndFun(varName, sDom, kCod, rng) when varName = x ->
                KIndFun(varName, sDom.subst(a,x), kCod, rng)
            | KIndFun(varName, sDom, kCod, rng) ->
                // rename the bound variable if it would capture a
                let varName' =
                    match a.freeVars.Contains varName with
                    | true ->
                        freshVar (Set.add x (Set.union a.freeVars kCod.freeIndVars)) varName
                    | false ->
                        varName
                let kCod' = kCod.rename(varName, varName')
                KIndFun(varName', sDom.subst(a,x), kCod'.subst(a,x), rng)

        /// Rename the free index variable x to x'
        member this.rename(x : string, x' : string) : Kind =
            match x = x' with
            | true ->
                this
            | false ->
                this.subst(AtomVar x', x)

        member this.Range : Range =
            match this with
            | KProper(rng)
            | KProperPopulated(rng)
            | KTyFun(_,_,rng)
            | KIndFun(_,_,_,rng) ->
                rng

type Ty =
    | TyDict of keyVarName : string * keySort : StrSort * domTy : Ty * Range
    | TyRecord of List<string * Ty> * Range
    | TyStringRef of selfVarName : string * boundSort : StrSort * formula : Formula * Range
    | TyIndAbs of varName : string * domSort : Sort * codTy : Ty * Range
    | TyTyAbs of varName : string * domKind : Kind * codTy : Ty * Range
    | TyUnion of indTyFun : Ty * Range
    | TyTyApp of fn : Ty * arg : Ty * Range
    | TyIndApp of fn : Ty * arg : Atom * Range
    | TyVar of name : string * Range
    | TyLet of name : string * rhsTy : Ty * bodyTy : Ty * Range

    with

        member this.freeIndVars : Set<string> =
            match this with
            | TyDict(keyVarName, _, domTy, _) ->
                Set.remove keyVarName domTy.freeIndVars
            | TyRecord(fields, _) ->
                Set.unionMany (List.map (fun (_, ty : Ty) -> ty.freeIndVars) fields)
            | TyStringRef(selfVarName, _, formula, _) ->
                Set.remove selfVarName formula.freeVars
            | TyIndAbs(varName, domSort, codTy, _) ->
                Set.union domSort.freeVars (Set.remove varName codTy.freeIndVars)
            | TyTyAbs(_, domKind, codTy, _) ->
                Set.union domKind.freeIndVars codTy.freeIndVars
            | TyUnion(indTyFun, _) ->
                indTyFun.freeIndVars
            | TyTyApp(fn, arg, _) ->
                Set.union fn.freeIndVars arg.freeIndVars
            | TyIndApp(fn, arg, _) ->
                Set.union fn.freeIndVars arg.freeVars
            | TyVar(_, _) ->
                Set.empty
            | TyLet(_, rhsTy, bodyTy, _) ->
                Set.union rhsTy.freeIndVars bodyTy.freeIndVars

        member this.freeTyVars : Set<string> =
            match this with
            | TyDict(_, _, domTy, _) ->
                domTy.freeTyVars
            | TyRecord(fields, _) ->
                Set.unionMany (List.map (fun (_, ty : Ty) -> ty.freeTyVars) fields)
            | TyStringRef(_, _, _, _) ->
                Set.empty
            | TyIndAbs(_, _, codTy, _) ->
                codTy.freeTyVars
            | TyTyAbs(varName, _, codTy, _) ->
                Set.remove varName codTy.freeTyVars
            | TyUnion(indTyFun, _) ->
                indTyFun.freeTyVars
            | TyTyApp(fn, arg, _) ->
                Set.union fn.freeTyVars arg.freeTyVars
            | TyIndApp(fn, _, _) ->
                fn.freeTyVars
            | TyVar(name, _) ->
                Set.singleton name
            | TyLet(name, rhsTy, bodyTy, _) ->
                Set.union rhsTy.freeTyVars (Set.remove name bodyTy.freeTyVars)

        member this.String : string =
            match this with
            | TyDict(keyVarName, keySort, domTy, _) ->
                /// the propositions guarding the dictionary's keys, followed by the type of its values
                let rec splitGuards (ty : Ty) : List<Formula> * Ty =
                    match ty with
                    | TyUnion(TyIndAbs(_, StProof(formula, _), codTy, _), _) ->
                        let guards, valTy = splitGuards codTy
                        (formula :: guards, valTy)
                    | _ ->
                        ([], ty)
                let guards, valTy = splitGuards domTy
                let guardsStr = String.concat "," <| List.map (fun (guard : Formula) -> " " + guard.String) guards
                "{ [" + keyVarName + " : " + keySort.String + "]" + guardsStr + " : " + valTy.String + " }"
            | TyRecord(fields, _) ->
                let fieldToString ((name, ty) : string * Ty) =
                    name + " : " + ty.String
                "{ " + (String.concat ", " <| List.map fieldToString fields) + " }"
            | TyStringRef(selfVarName, boundSort, formula, _) ->
                "{ " + selfVarName + " : " + boundSort.String + " | " + formula.String + " }"
            | TyIndAbs(varName, domSort, codTy, _) ->
                "(" + varName + " : " + domSort.String + ") => " + codTy.String
            | TyTyAbs(varName, domKind, codTy, _) ->
                "(" + varName + " :: " + domKind.String + ") => " + codTy.String
            | TyUnion(TyIndAbs(_, StPred(_, _), _, _), _) ->
                /// the predicates defined by a block, followed by the block's scope
                let rec splitPredicates (ty : Ty) : List<string * PredSig> * Ty =
                    match ty with
                    | TyUnion(TyIndAbs(varName, StPred(predSig, _), codTy, _), _) ->
                        let defs, scope = splitPredicates codTy
                        ((varName, predSig) :: defs, scope)
                    | _ ->
                        ([], ty)
                let defs, scope = splitPredicates this
                let defsStr = String.concat " " <| List.map (fun (name, predSig : PredSig) -> name + predSig.String) defs
                "predicates " + defsStr + " end " + scope.String
            | TyUnion(indTyFun, _) ->
                // only predicates and dictionary guards have a concrete syntax
                "union " + indTyFun.String
            | TyTyApp(fn, arg, _) ->
                "(" + fn.String + " !" + arg.String + ")"
            | TyIndApp(fn, arg, _) ->
                "(" + fn.String + " " + arg.String + ")"
            | TyVar(name, _) ->
                name
            | TyLet(boundVarName, rhsTy, bodyTy, _) ->
                "type " + boundVarName + " = " + rhsTy.String + " in\n" + bodyTy.String

        /// Substitute a for the index variable varName in this
        member this.substInd(varName : string, a : Atom) : Ty =
            /// Renames the index variable *boundVar*, which is bound in a scope whose free index
            /// variables are *scopeVars*, if it would capture a
            let avoidCapture (boundVar : string) (scopeVars : Set<string>) : string =
                match a.freeVars.Contains boundVar with
                | true ->
                    freshVar (Set.add varName (Set.union a.freeVars scopeVars)) boundVar
                | false ->
                    boundVar

            match this with
            | TyDict(keyVarName, _, _, _) when keyVarName = varName ->
                this
            | TyDict(keyVarName, keySort, domTy, rng) ->
                let keyVarName' = avoidCapture keyVarName domTy.freeIndVars
                let domTy' = domTy.renameInd(keyVarName, keyVarName')
                TyDict(keyVarName', keySort, domTy'.substInd(varName, a), rng)
            | TyRecord(fields, rng) ->
                TyRecord(List.map (fun (x : string, T : Ty) -> (x, T.substInd(varName, a))) fields, rng)
            | TyStringRef(selfVarName, _, _, _) when selfVarName = varName ->
                this
            | TyStringRef(selfVarName, boundSort, formula, rng) ->
                let selfVarName' = avoidCapture selfVarName formula.freeVars
                let formula' = formula.subst(AtomVar selfVarName', selfVarName)
                TyStringRef(selfVarName', boundSort, formula'.subst(a, varName), rng)
            | TyIndAbs(absVarName, domSort, codTy, rng) when absVarName = varName ->
                TyIndAbs(absVarName, domSort.subst(a, varName), codTy, rng)
            | TyIndAbs(absVarName, domSort, codTy, rng) ->
                let absVarName' = avoidCapture absVarName codTy.freeIndVars
                let codTy' = codTy.renameInd(absVarName, absVarName')
                TyIndAbs(absVarName', domSort.subst(a, varName), codTy'.substInd(varName, a), rng)
            | TyTyAbs(absVarName, domKind, codTy, rng) ->
                TyTyAbs(absVarName, domKind.subst(a, varName), codTy.substInd(varName, a), rng)
            | TyUnion(indTyFun, rng) ->
                TyUnion(indTyFun.substInd(varName, a), rng)
            | TyTyApp(fn, arg, rng) ->
                TyTyApp(fn.substInd(varName, a), arg.substInd(varName, a), rng)
            | TyIndApp(fn, arg, rng) ->
                TyIndApp(fn.substInd(varName, a), arg.subst(a, varName), rng)
            | TyVar(_, _) ->
                this
            | TyLet(boundVarName, rhsTy, bodyTy, rng) ->
                TyLet(boundVarName, rhsTy.substInd(varName, a), bodyTy.substInd(varName, a), rng)

        /// Rename the free index variable x to x'
        member this.renameInd(x : string, x' : string) : Ty =
            match x = x' with
            | true ->
                this
            | false ->
                this.substInd(x, AtomVar x')

        /// Substitute other for the type variable varName in this
        member this.substTy(varName : string, other : Ty) : Ty =
            let otherIndVars = other.freeIndVars
            let otherTyVars = other.freeTyVars

            /// Renames the index variable x, whose scope is body, if it would capture
            /// one of other's free index variables
            let avoidIndCapture (x : string) (body : Ty) : string * Ty =
                match otherIndVars.Contains x with
                | true ->
                    let x' = freshVar (Set.union otherIndVars body.freeIndVars) x
                    (x', body.renameInd(x, x'))
                | false ->
                    (x, body)

            /// Renames the type variable x, whose scope is body, if it would capture
            /// one of other's free type variables
            let avoidTyCapture (x : string) (body : Ty) : string * Ty =
                match otherTyVars.Contains x with
                | true ->
                    let x' = freshVar (Set.add varName (Set.union otherTyVars body.freeTyVars)) x
                    (x', body.substTy(x, TyVar(x', noRange)))
                | false ->
                    (x, body)

            let rec subst (ty : Ty) : Ty =
                match ty with
                | TyDict(keyVarName, keySort, domTy, rng) ->
                    let keyVarName', domTy' = avoidIndCapture keyVarName domTy
                    TyDict(keyVarName', keySort, subst domTy', rng)
                | TyRecord(fields, rng) ->
                    TyRecord(List.map (fun (name : string, fieldTy : Ty) -> (name, subst fieldTy)) fields, rng)
                | TyStringRef(_, _, _, _) ->
                    ty
                | TyIndAbs(absVar, domSort, codTy, rng) ->
                    let absVar', codTy' = avoidIndCapture absVar codTy
                    TyIndAbs(absVar', domSort, subst codTy', rng)
                | TyTyAbs(absVar, _, _, _) when absVar = varName ->
                    ty
                | TyTyAbs(absVar, domKind, codTy, rng) ->
                    let absVar', codTy' = avoidTyCapture absVar codTy
                    TyTyAbs(absVar', domKind, subst codTy', rng)
                | TyUnion(indTyFun, rng) ->
                    TyUnion(subst indTyFun, rng)
                | TyTyApp(fn, arg, rng) ->
                    TyTyApp(subst fn, subst arg, rng)
                | TyIndApp(fn, arg, rng) ->
                    TyIndApp(subst fn, arg, rng)
                | TyVar(name, _) when name = varName ->
                    other // TODO: maybe replace all ranges in other with varRng
                | TyVar(_, _) ->
                    ty
                | TyLet(boundVar, rhsTy, bodyTy, rng) when boundVar = varName ->
                    TyLet(boundVar, subst rhsTy, bodyTy, rng)
                | TyLet(boundVar, rhsTy, bodyTy, rng) ->
                    let boundVar', bodyTy' = avoidTyCapture boundVar bodyTy
                    TyLet(boundVar', subst rhsTy, subst bodyTy', rng)

            subst this

        member this.Range : Range =
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

type KindContext = Map<string, Kind>

/// Bindings of index variables, innermost first.
///
/// Invariant: no variable other than "_" is bound twice. Sorts and proofs in a context are compared
/// syntactically, so a shadowed variable would be confused with the variable shadowing it. The
/// "enter" functions below maintain this invariant; use them before extending a context.
type SortContext = List<string * Sort>

/// Chooses the name under which the binder *varName* is added to sctxt. This is *varName* unless
/// sctxt already binds it. *scopeVars* are the free index variables of the binder's scope.
let private nameForBinder (sctxt : SortContext) (varName : string) (scopeVars : Set<string>) : string =
    match varName <> "_" && List.exists (fun (x, _) -> x = varName) sctxt with
    | true ->
        freshVar (Set.union scopeVars (Set.ofList <| List.map fst sctxt)) varName
    | false ->
        varName

/// Prepares to add a binder of the index variable *varName*, whose scope is *body*, to sctxt.
/// Returns the binder's name and scope, alpha-renamed if sctxt already binds *varName*.
let enterTy (sctxt : SortContext) (varName : string) (body : Ty) : string * Ty =
    let varName' = nameForBinder sctxt varName body.freeIndVars
    (varName', body.renameInd(varName, varName'))

/// Like enterTy, for a binder whose scope is a kind
let enterKind (sctxt : SortContext) (varName : string) (body : Kind) : string * Kind =
    let varName' = nameForBinder sctxt varName body.freeIndVars
    (varName', body.rename(varName, varName'))

/// Like enterTy, for a binder whose scope is a predicate application
let enterPredApp (sctxt : SortContext) (varName : string) (body : PredApp) : string * PredApp =
    let varName' = nameForBinder sctxt varName body.freeVars
    match varName' = varName with
    | true ->
        (varName, body)
    | false ->
        (varName', body.subst(AtomVar varName', varName))

/// Like enterTy, for a binder whose scope is a formula
let enterFormula (sctxt : SortContext) (varName : string) (body : Formula) : string * Formula =
    match body with
    | FmTrue ->
        (nameForBinder sctxt varName Set.empty, FmTrue)
    | FmApp(app) ->
        let varName', app' = enterPredApp sctxt varName app
        (varName', FmApp(app'))

/// Like enterTy, for the string formals of a predicate signature, whose scope is its proof section
let enterPredSig (sctxt : SortContext) (predSig : PredSig) : PredSig =
    predSig.renameFormals(Set.ofList <| List.map fst sctxt)

type DecisionProcedureKey =
    /// We must use the string denoted by the variable varName at this position
    | ArgumentKey of varName : string
    /// we must use the string lit as the key at this position
    | LiteralKey of lit : string
    /// this is the refinement variable; we must use the value @loc here
    | Refinement

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
    proofs : Set<PredApp>

    // the sequence of lookups needed to decide the set of proofs
    keys : List<DecisionProcedureKey>
}

type Satellite =
    /// all of the information necessary to create a decision procedure for a predicate in context
    | DecisionProcedure of CanonicalSortContext
    /// we require a decision procedure for this predicate before the variable this satellite is attached to goes out of scope
    | DecisionProcedureRequirement of CanonicalSortContext

/// A sort context whose bindings have been sorted into sections, like the formals of a predicate
and CanonicalSortContext = {
    // ------- Predicate section -------

    /// Bindings with predicate sorts
    //predicates : List<string * Sort * Set<Satellite>>
    predicates : List<string * PredSig>

    // ------- String section -------

    /// Bindings with string sorts, outermost first
    // to simplify, all strings are physical. I'm not sure if non-physical strings are useful.
    // we can just normalize before running the validation generator
    strings : List<string * StrSort>

    // ------- Proof section -------

    /// Set of propositions that our context contains proofs of
    proofs : Set<PredApp>
}

    with
        member this.String =
            let strings' = List.filter (fun (x : string,st) -> x <> "" && x.[0] <> '_') this.strings
            let stringsStr = String.concat " , " <| List.map (fun (x,st : StrSort) -> sprintf "%s : %s" x st.String) strings'
            let predsStr = String.concat " , " <| List.map (fun (x,st : PredSig) -> sprintf "%s%s" x st.String) this.predicates
            sprintf "strings: %s\npredicates: %s\nproofs: %s" stringsStr predsStr this.StringProofs

        member this.StringProofs =
            String.concat "," (Seq.map (fun (app : PredApp) -> app.String)
                              (Set.toSeq this.proofs))

        static member empty : CanonicalSortContext =
            {
                predicates = []
                strings = []
                proofs = Set.empty
            }


type DecisionSite = {
    sctxt : CanonicalSortContext
    selfVar : string
    selfSort : StrSort
    formulaToDecide : PredApp
}
    with
        member this.String =
            sprintf "%s\nselfVar: %s\nselfSort: %s\nformulaToDecide: %s" this.sctxt.String this.selfVar this.selfSort.String this.formulaToDecide.String


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
    propSet : Set<PredApp>

    /// a context containing all variables as predicates occuring in the propSet
    args : SortContext

}

type AppClassifier =
    | IndToTy
    | TyToTy
