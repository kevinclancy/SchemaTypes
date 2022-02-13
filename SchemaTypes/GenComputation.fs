module GenComputation

open FSharp.Text.Lexing
open Syntax
open MCode
open DecisionProcedures

type Range = Position * Position

let noPos : Position = {
    pos_fname = ""
    pos_lnum = 0
    pos_bol = 0
    pos_cnum = 0
}

let noRange = (noPos, noPos)

type GenState = {
    /// the next identifier for a decision procedure call site
    nextId : int
    
    /// decision procedure requirements
    reqs : Set<int * CanonicalSortContext>  

    /// decision procedure suppliers
    suppliers: Set<CanonicalSortContext>
}

type GenState with
    static member Empty =
        { nextId = 0 ; reqs = Set.empty ; suppliers = Set.empty }

type Outcome<'A> = 
    | Result of 'A * GenState
    | Error of string

type Gen<'A> = GenState -> Outcome<'A>
        
type GenBuilder () =
    member x.Bind(comp : Gen<'A>, func : 'A -> Gen<'B>) : Gen<'B> =
        (fun genState -> 
            match comp genState with 
            | Result(a, s') -> func a s'
            | Error(msg) -> Error(msg) 
        )

    member x.Return(value : 'A) : Gen<'A> =
        (fun genState -> Result (value, genState))

    member x.Zero() : Gen<unit> =
        (fun genState -> Result ((), genState))

let gen = new GenBuilder()

let error (msg : string) (s : GenState) : Outcome<'A> =
    Error msg

let pass (s : GenState) : Outcome<unit> =
    Result ((), s)

/// Returns the set of all decision procedure requirements
let getReqs (s : GenState) : Outcome<Set<int * CanonicalSortContext>> =
    Result (s.reqs, s)

/// adds a new decision procedure requirement, returning its identifier
let addReq (sctxt : CanonicalSortContext) (s : GenState) : Outcome<int> =
    Result (s.nextId, { s with reqs = s.reqs.Add(s.nextId, sctxt) ; nextId = s.nextId + 1 })

/// Returns the set of decision procedure suppliers
let getSuppliers (s : GenState) : Outcome<Set<CanonicalSortContext>> =
   Result (s.suppliers, s) 

/// adds a new decision procedure supplier
let addSupplier (sctxt : CanonicalSortContext) (s : GenState) : Outcome<unit> =
    Result ((), { s with suppliers = s.suppliers.Add(sctxt) })

/// removes all suppliers and requirements that include applications of the predicate *predName*
/// returns them in the result as (requirements, suppliers)
let removePred (predName : string) (s : GenState) : Outcome< Set<int * CanonicalSortContext> * Set<CanonicalSortContext> > =

    let appliesPred (ind : Index) =
        match ind with
        | FlatApp(func, args) when func = predName ->
            true
        | _ ->
            false

    let foldReq ((take, leave) : Set<int * CanonicalSortContext> * Set<int * CanonicalSortContext>) 
                ((i, sctxt) : int * CanonicalSortContext) =

        match Set.exists appliesPred sctxt.proofs with
        | true ->
            (take.Add (i, sctxt), leave)
        | false ->
            (take, leave.Add (i, sctxt))

    let takeReqs, leaveReqs = Set.fold foldReq (Set.empty, Set.empty) s.reqs
    
    let foldSupplier ((take, leave) : Set<CanonicalSortContext> * Set<CanonicalSortContext>)
                     (sctxt : CanonicalSortContext) = 

        match Set.exists appliesPred sctxt.proofs with
        | true ->
            (take.Add sctxt, leave)
        | false ->
            (take, leave.Add sctxt)

    let takeSupp, leaveSupp = Set.fold foldSupplier (Set.empty, Set.empty) s.suppliers

    Result ((takeReqs, takeSupp), { s with reqs = leaveReqs ; suppliers = leaveSupp })

let rec fold (init : 'S) (f : 'S -> 'A -> 'S) (l : List<Gen<'A>>) : Gen<'S> =
    match l with
    | fst :: rest ->
        gen {
            let! a = fst
            let! s = fold init f rest
            return (f s a)
        }
    | [] ->
        gen {
            return init
        }

let rec foldM (init : 'S) (f : 'S -> 'A -> Gen<'S>) (l : List<'A>) : Gen<'S> =
    match l with
    | first :: rest ->
        gen {
            let! s1 = f init first
            let! s2 = foldM s1 f rest
            return s2
        }
    | [] ->
        gen {
            return init
        }

let rec map (f : 'A -> 'B) (l : List<Gen<'A>>) : Gen<List<'B>> =
    match l with
    | fst :: rest ->
        gen {
            let! a = fst
            let! b = map f rest
            return (f a) :: b
        }
    | [] ->
        gen {
            return []
        }

let rec letAll (l : List<Gen<'A>>) : Gen<List<'A>> =
    match l with
    | fst :: rest ->
        gen {
            let! a = fst
            let! b = letAll rest
            return a :: b
        }
    | [] ->
        gen {
            return []
        }

let rec doAll (l : List<Gen<unit>>) : Gen<unit> =
    match l with
    | fst :: rest ->
        gen {
            do! fst
            do! doAll rest
            return ()
        }
    | [] ->
        gen {
            return ()
        }