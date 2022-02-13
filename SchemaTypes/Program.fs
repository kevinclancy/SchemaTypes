// Learn more about F# at http://fsharp.org

open System

open Syntax
open System.IO
open FSharp.Text.Lexing
open KindCheck
open CheckComputation
open Eval
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

[<EntryPoint>]
let main argv =
    try
        let reader = new StreamReader(argv.[0])
        let lexbuffer : LexBuffer<char> = LexBuffer<char>.FromString(reader.ReadToEnd())
        let src = (new StreamReader(argv.[0])).ReadToEnd()
        let ty =
            try
                Parser.ty (Lexer.token) lexbuffer
            with
            | e ->
                let message = e.Message
                printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) (lexbuffer.StartPos.Column)
                exit 1
        match kindSynth [] Map.empty ty with
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
