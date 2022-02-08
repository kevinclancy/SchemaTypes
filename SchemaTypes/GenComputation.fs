module GenComputation

open FSharp.Text.Lexing
open Syntax
open MCode

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

type Gen<'A> = GenState -> 'A * GenState
        
type GenBuilder () =
    member x.Bind(comp : Gen<'A>, func : 'A -> Gen<'B>) : Gen<'B> =
        (fun genState -> let (a,s') = comp genState in func a s')

    member x.Return(value : 'A) : Gen<'A> =
        (fun genState -> (value, genState))

let gen = new GenBuilder()

/// Returns the set of all decision procedure requirements
let getProcReqs (s : GenState) : Set<int * CanonicalSortContext> * GenState =
    (s.reqs, s)

/// adds a new decision procedure requirement, returning its identifier
let addProcReq (sctxt : CanonicalSortContext) (s : GenState) : int * GenState =
    (s.nextId, { s with reqs = s.reqs.Add(s.nextId, sctxt) ; nextId = s.nextId + 1 })

/// Returns the set of decision procedure suppliers
let getSuppliers (s : GenState) : Set<CanonicalSortContext> * GenState =
   (s.suppliers, s) 

/// adds a new decision procedure supplier
let addSupplier (sctxt : CanonicalSortContext) (s : GenState) : unit * GenState =
    ((), { s with suppliers = s.suppliers.Add(sctxt) })

/// removes all suppliers and requirements that include applications of the predicate *predName*
/// returns them in the result as (requirements, suppliers)
let removePred (predName : string) (s : GenState) : (Set<int * CanonicalSortContext> * Set<CanonicalSortContext>) * GenState =
    failwith "todo"

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