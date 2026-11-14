// Learn more about F# at http://fsharp.org

open System

open Surface.Syntax
open System.IO
open FSharp.Text.Lexing
open Surface.KindCheck
open CheckComputation
open Surface.Eval
open CodeGen

let rec printStack (stack : List<string*Range>) (level : int) =
    match stack with
    | (error, rng) :: rest when rng = noRange ->
        printfn "%s%s" (String.replicate (2 * level) " ") error
        printStack rest (level + 1)
    | (error,(startPos,_)) ::  rest ->
        let location = "line: " + (startPos.Line + 1).ToString() + " column: " + startPos.Column.ToString()
        let indent = String.replicate (2 * level) " "
        printfn ("%s%s\n  %s%s\n") indent location indent error
        printStack rest (level + 1)
    | [] ->
        ()

/// Compiles a well-kinded surface type to the core language, then kind checks and normalizes the result there
let checkCore (ty : Ty) : bool =
    let coreTy = Surface.Compile.compileTy ty
    printfn "core type: %s\n" coreTy.String
    match Core.KindCheck.kindSynth [] Map.empty coreTy with
    | Result(kind) ->
        printfn "core kind: %s\n" kind.String
        printfn "normalized core type: %s\n\n\n" (Core.Eval.normalize [] coreTy).String
        true
    | Error stack ->
        printfn "core type failed to kind check:"
        printStack stack 0
        false

[<EntryPoint>]
let main argv =
    try
        /// when this flag is provided, we also compile the schema to the core language and check it there
        let coreFlag = "--core"
        let fileName = (Array.filter (fun arg -> arg <> coreFlag) argv).[0]
        let reader = new StreamReader(fileName)
        let lexbuffer : LexBuffer<char> = LexBuffer<char>.FromString(reader.ReadToEnd())
        let src = (new StreamReader(fileName)).ReadToEnd()
        let ty =
            try
                Parser.ty (Lexer.token) lexbuffer
            with
            | e ->
                let message = e.Message
                printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) (lexbuffer.StartPos.Column)
                exit 1
        match kindSynth [] Map.empty ty with
        | Result(kind) when Array.contains coreFlag argv && not (checkCore ty) ->
            1
        | Result(kind) ->
            let normTy = normalize [] ty
            printfn "normalized type: %s\n\n\n" normTy.String
            match genCode [] normTy GenComputation.GenState.Empty with
            | GenComputation.Result((code, _), _) ->
                printfn "gen succeeded!\n\nvalidate\n%s" code.String
                0
            | GenComputation.Error msg ->
                printfn "error: %s" msg
                1
        | Error stack ->
            printStack stack 0
            1

    with
    | :? IndexOutOfRangeException ->
        printfn "provide the name of a text file as the command line argument"
        1
    | :? FileNotFoundException ->
        printfn "file not found"
        1
