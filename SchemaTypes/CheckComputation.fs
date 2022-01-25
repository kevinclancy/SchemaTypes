module CheckComputation

open FSharp.Text.Lexing

type Range = Position * Position

let noPos : Position = {
    pos_fname = ""
    pos_lnum = 0
    pos_bol = 0
    pos_cnum = 0
}

let noRange = (noPos, noPos)

type Check<'A> =
    | Error of List<string * Range>
    // | ValidPendingError of msg : string * rng : Range
    | Result of result : 'A

    member this.Succeeds =
        match this with
        | Result(_) ->
            true
        | _ ->
            false

    member this.GetResult =
        match this with
        | Result(v) ->
            v
        | _ ->
            failwith "computation fails; check Succeeds property before reading Result"
        
type CheckBuilder () =
    member x.Bind(comp : Check<'A>, func : 'A -> Check<'B>) =
        match comp with
        | Error(stack) ->
            Error(stack)
        | Result(r) ->
            func r

    member x.Return(value : 'A) : Check<'A> =
        Result(value)

let withError (msg : string) (rng : Range) (comp : Check<'A>) : Check<'A> =
    match comp with
    | Error(stack) ->
        Error( (msg,rng) :: stack )
    | Result(r) ->
        Result(r)
  
let rec sequence (l : List<Check<Unit>>) : Check<Unit> =
    match l with
    | Error(stack) :: _ ->
        Error(stack)
    | _ :: rest ->
        sequence rest
    | [] ->
        Result ()
let check = new CheckBuilder()

let rec fold (init : 'S) (f : 'S -> 'A -> 'S) (l : List<Check<'A>>) : Check<'S> =
    match l with
    | fst :: rest ->
        check {
            let! a = fst
            let! s = fold init f rest
            return (f s a)
        }
    | [] ->
        check {
            return init
        }

let rec foldM (init : 'S) (f : 'S -> 'A -> Check<'S>) (l : List<'A>) : Check<'S> =
    match l with
    | first :: rest ->
        check {
            let! s1 = f init first
            let! s2 = foldM s1 f rest
            return s2
        }
    | [] ->
        check {
            return init
        }

let rec map (f : 'A -> 'B) (l : List<Check<'A>>) : Check<List<'B>> =
    match l with
    | fst :: rest ->
        check {
            let! a = fst
            let! b = map f rest
            return (f a) :: b
        }
    | [] ->
        check {
            return []
        }

let rec letAll (l : List<Check<'A>>) : Check<List<'A>> =
    match l with
    | fst :: rest ->
        check {
            let! a = fst
            let! b = letAll rest
            return a :: b
        }
    | [] ->
        check {
            return []
        }

let rec doAll (l : List<Check<unit>>) : Check<unit> =
    match l with
    | fst :: rest ->
        check {
            do! fst
            do! doAll rest
            return ()
        }
    | [] ->
        check {
            return ()
        }