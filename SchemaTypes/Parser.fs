// Implementation file for parser generated by fsyacc
module Parser
#nowarn "64";; // turn off warnings that type variables used in production annotations are instantiated to concrete type
open FSharp.Text.Lexing
open FSharp.Text.Parsing.ParseHelpers
# 1 "Parser.fsy"

open System
open Syntax


# 12 "Parser.fs"
// This type is the type of tokens accepted by the parser
type token = 
  | LBRACK
  | RBRACK
  | JOIN
  | DOT
  | BACKSLASH
  | LBARBRACK
  | RBARBRACK
  | LANGLE
  | RANGLE
  | EOF
  | STR
  | PROP
  | PROOF
  | TO
  | LPAREN
  | RPAREN
  | COLON
  | TRUE
  | RSQUAREBRACK
  | LSQUAREBRACK of (string)
  | STRLITERAL of (string)
  | INT of (int)
  | CHAR of (char)
  | ID of (string*string)
// This type is used to give symbolic names to token indexes, useful for error messages
type tokenId = 
    | TOKEN_LBRACK
    | TOKEN_RBRACK
    | TOKEN_JOIN
    | TOKEN_DOT
    | TOKEN_BACKSLASH
    | TOKEN_LBARBRACK
    | TOKEN_RBARBRACK
    | TOKEN_LANGLE
    | TOKEN_RANGLE
    | TOKEN_EOF
    | TOKEN_STR
    | TOKEN_PROP
    | TOKEN_PROOF
    | TOKEN_TO
    | TOKEN_LPAREN
    | TOKEN_RPAREN
    | TOKEN_COLON
    | TOKEN_TRUE
    | TOKEN_RSQUAREBRACK
    | TOKEN_LSQUAREBRACK
    | TOKEN_STRLITERAL
    | TOKEN_INT
    | TOKEN_CHAR
    | TOKEN_ID
    | TOKEN_end_of_input
    | TOKEN_error
// This type is used to give symbolic names to token indexes, useful for error messages
type nonTerminalId = 
    | NONTERM__startindex
    | NONTERM__startsort
    | NONTERM_sort
    | NONTERM_Sort
    | NONTERM_IndAppList
    | NONTERM_SimpleIndex
    | NONTERM_index
    | NONTERM_Index

// This function maps tokens to integer indexes
let tagOfToken (t:token) = 
  match t with
  | LBRACK  -> 0 
  | RBRACK  -> 1 
  | JOIN  -> 2 
  | DOT  -> 3 
  | BACKSLASH  -> 4 
  | LBARBRACK  -> 5 
  | RBARBRACK  -> 6 
  | LANGLE  -> 7 
  | RANGLE  -> 8 
  | EOF  -> 9 
  | STR  -> 10 
  | PROP  -> 11 
  | PROOF  -> 12 
  | TO  -> 13 
  | LPAREN  -> 14 
  | RPAREN  -> 15 
  | COLON  -> 16 
  | TRUE  -> 17 
  | RSQUAREBRACK  -> 18 
  | LSQUAREBRACK _ -> 19 
  | STRLITERAL _ -> 20 
  | INT _ -> 21 
  | CHAR _ -> 22 
  | ID _ -> 23 

// This function maps integer indexes to symbolic token ids
let tokenTagToTokenId (tokenIdx:int) = 
  match tokenIdx with
  | 0 -> TOKEN_LBRACK 
  | 1 -> TOKEN_RBRACK 
  | 2 -> TOKEN_JOIN 
  | 3 -> TOKEN_DOT 
  | 4 -> TOKEN_BACKSLASH 
  | 5 -> TOKEN_LBARBRACK 
  | 6 -> TOKEN_RBARBRACK 
  | 7 -> TOKEN_LANGLE 
  | 8 -> TOKEN_RANGLE 
  | 9 -> TOKEN_EOF 
  | 10 -> TOKEN_STR 
  | 11 -> TOKEN_PROP 
  | 12 -> TOKEN_PROOF 
  | 13 -> TOKEN_TO 
  | 14 -> TOKEN_LPAREN 
  | 15 -> TOKEN_RPAREN 
  | 16 -> TOKEN_COLON 
  | 17 -> TOKEN_TRUE 
  | 18 -> TOKEN_RSQUAREBRACK 
  | 19 -> TOKEN_LSQUAREBRACK 
  | 20 -> TOKEN_STRLITERAL 
  | 21 -> TOKEN_INT 
  | 22 -> TOKEN_CHAR 
  | 23 -> TOKEN_ID 
  | 26 -> TOKEN_end_of_input
  | 24 -> TOKEN_error
  | _ -> failwith "tokenTagToTokenId: bad token"

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
let prodIdxToNonTerminal (prodIdx:int) = 
  match prodIdx with
    | 0 -> NONTERM__startindex 
    | 1 -> NONTERM__startsort 
    | 2 -> NONTERM_sort 
    | 3 -> NONTERM_Sort 
    | 4 -> NONTERM_Sort 
    | 5 -> NONTERM_Sort 
    | 6 -> NONTERM_Sort 
    | 7 -> NONTERM_IndAppList 
    | 8 -> NONTERM_IndAppList 
    | 9 -> NONTERM_SimpleIndex 
    | 10 -> NONTERM_SimpleIndex 
    | 11 -> NONTERM_SimpleIndex 
    | 12 -> NONTERM_index 
    | 13 -> NONTERM_Index 
    | 14 -> NONTERM_Index 
    | _ -> failwith "prodIdxToNonTerminal: bad production index"

let _fsyacc_endOfInputTag = 26 
let _fsyacc_tagOfErrorTerminal = 24

// This function gets the name of a token as a string
let token_to_string (t:token) = 
  match t with 
  | LBRACK  -> "LBRACK" 
  | RBRACK  -> "RBRACK" 
  | JOIN  -> "JOIN" 
  | DOT  -> "DOT" 
  | BACKSLASH  -> "BACKSLASH" 
  | LBARBRACK  -> "LBARBRACK" 
  | RBARBRACK  -> "RBARBRACK" 
  | LANGLE  -> "LANGLE" 
  | RANGLE  -> "RANGLE" 
  | EOF  -> "EOF" 
  | STR  -> "STR" 
  | PROP  -> "PROP" 
  | PROOF  -> "PROOF" 
  | TO  -> "TO" 
  | LPAREN  -> "LPAREN" 
  | RPAREN  -> "RPAREN" 
  | COLON  -> "COLON" 
  | TRUE  -> "TRUE" 
  | RSQUAREBRACK  -> "RSQUAREBRACK" 
  | LSQUAREBRACK _ -> "LSQUAREBRACK" 
  | STRLITERAL _ -> "STRLITERAL" 
  | INT _ -> "INT" 
  | CHAR _ -> "CHAR" 
  | ID _ -> "ID" 

// This function gets the data carried by a token as an object
let _fsyacc_dataOfToken (t:token) = 
  match t with 
  | LBRACK  -> (null : System.Object) 
  | RBRACK  -> (null : System.Object) 
  | JOIN  -> (null : System.Object) 
  | DOT  -> (null : System.Object) 
  | BACKSLASH  -> (null : System.Object) 
  | LBARBRACK  -> (null : System.Object) 
  | RBARBRACK  -> (null : System.Object) 
  | LANGLE  -> (null : System.Object) 
  | RANGLE  -> (null : System.Object) 
  | EOF  -> (null : System.Object) 
  | STR  -> (null : System.Object) 
  | PROP  -> (null : System.Object) 
  | PROOF  -> (null : System.Object) 
  | TO  -> (null : System.Object) 
  | LPAREN  -> (null : System.Object) 
  | RPAREN  -> (null : System.Object) 
  | COLON  -> (null : System.Object) 
  | TRUE  -> (null : System.Object) 
  | RSQUAREBRACK  -> (null : System.Object) 
  | LSQUAREBRACK _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
  | STRLITERAL _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
  | INT _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
  | CHAR _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
  | ID _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
let _fsyacc_gotos = [| 0us;65535us;0us;65535us;1us;65535us;2us;3us;3us;65535us;2us;4us;12us;13us;15us;16us;1us;65535us;26us;17us;4us;65535us;0us;25us;8us;25us;17us;18us;26us;19us;1us;65535us;0us;1us;2us;65535us;0us;23us;8us;9us;|]
let _fsyacc_sparseGotoTableRowOffsets = [|0us;1us;2us;4us;8us;10us;15us;17us;|]
let _fsyacc_stateToProdIdxsTableElements = [| 1us;0us;1us;0us;1us;1us;1us;1us;1us;2us;1us;2us;1us;3us;1us;4us;1us;5us;1us;5us;1us;6us;1us;6us;1us;6us;1us;6us;1us;6us;1us;6us;1us;6us;2us;7us;14us;1us;7us;1us;8us;1us;9us;1us;10us;1us;11us;1us;12us;1us;12us;1us;13us;1us;14us;1us;14us;|]
let _fsyacc_stateToProdIdxsTableRowOffsets = [|0us;2us;4us;6us;8us;10us;12us;14us;16us;18us;20us;22us;24us;26us;28us;30us;32us;34us;37us;39us;41us;43us;45us;47us;49us;51us;53us;55us;|]
let _fsyacc_action_rows = 28
let _fsyacc_actionTableElements = [|4us;32768us;14us;26us;17us;22us;20us;20us;23us;21us;0us;49152us;4us;32768us;10us;6us;11us;7us;12us;8us;14us;10us;0us;49152us;1us;32768us;9us;5us;0us;16386us;0us;16387us;0us;16388us;4us;32768us;14us;26us;17us;22us;20us;20us;23us;21us;0us;16389us;1us;32768us;23us;11us;1us;32768us;16us;12us;4us;32768us;10us;6us;11us;7us;12us;8us;14us;10us;1us;32768us;15us;14us;1us;32768us;13us;15us;4us;32768us;10us;6us;11us;7us;12us;8us;14us;10us;0us;16390us;4us;32768us;15us;27us;17us;22us;20us;20us;23us;21us;0us;16391us;0us;16392us;0us;16393us;0us;16394us;0us;16395us;1us;32768us;9us;24us;0us;16396us;0us;16397us;3us;32768us;17us;22us;20us;20us;23us;21us;0us;16398us;|]
let _fsyacc_actionTableRowOffsets = [|0us;5us;6us;11us;12us;14us;15us;16us;17us;22us;23us;25us;27us;32us;34us;36us;41us;42us;47us;48us;49us;50us;51us;52us;54us;55us;56us;60us;|]
let _fsyacc_reductionSymbolCounts = [|1us;1us;2us;1us;1us;2us;7us;2us;1us;1us;1us;1us;2us;1us;3us;|]
let _fsyacc_productionToNonTerminalTable = [|0us;1us;2us;3us;3us;3us;3us;4us;4us;5us;5us;5us;6us;7us;7us;|]
let _fsyacc_immediateActions = [|65535us;49152us;65535us;49152us;65535us;16386us;16387us;16388us;65535us;16389us;65535us;65535us;65535us;65535us;65535us;65535us;16390us;65535us;16391us;16392us;16393us;16394us;16395us;65535us;16396us;16397us;65535us;16398us;|]
let _fsyacc_reductions = lazy [|
# 226 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> Index in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
                      raise (FSharp.Text.Parsing.Accept(Microsoft.FSharp.Core.Operators.box _1))
                   )
                 : 'gentype__startindex));
# 235 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> Sort in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
                      raise (FSharp.Text.Parsing.Accept(Microsoft.FSharp.Core.Operators.box _1))
                   )
                 : 'gentype__startsort));
# 244 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Sort in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 30 "Parser.fsy"
                                       _1 
                   )
# 30 "Parser.fsy"
                 : Sort));
# 255 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 32 "Parser.fsy"
                                  StString(parseState.ResultRange) 
                   )
# 32 "Parser.fsy"
                 : 'gentype_Sort));
# 265 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 33 "Parser.fsy"
                                   StProp(parseState.ResultRange) 
                   )
# 33 "Parser.fsy"
                 : 'gentype_Sort));
# 275 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> 'gentype_Index in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 34 "Parser.fsy"
                                          StProof(_2, parseState.ResultRange) 
                   )
# 34 "Parser.fsy"
                 : 'gentype_Sort));
# 286 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> string*string in
            let _4 = parseState.GetInput(4) :?> 'gentype_Sort in
            let _7 = parseState.GetInput(7) :?> 'gentype_Sort in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 35 "Parser.fsy"
                                                                  StFun(snd _2, _4, _7, parseState.ResultRange) 
                   )
# 35 "Parser.fsy"
                 : 'gentype_Sort));
# 299 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_IndAppList in
            let _2 = parseState.GetInput(2) :?> 'gentype_SimpleIndex in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 37 "Parser.fsy"
                                                           IndApp(_1, _2, parseState.ResultRange) 
                   )
# 37 "Parser.fsy"
                 : 'gentype_IndAppList));
# 311 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_SimpleIndex in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 38 "Parser.fsy"
                                                _1 
                   )
# 38 "Parser.fsy"
                 : 'gentype_IndAppList));
# 322 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> string in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 40 "Parser.fsy"
                                                IndStringLit(_1, parseState.ResultRange) 
                   )
# 40 "Parser.fsy"
                 : 'gentype_SimpleIndex));
# 333 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> string*string in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 41 "Parser.fsy"
                                        IndVar(snd _1, parseState.ResultRange) 
                   )
# 41 "Parser.fsy"
                 : 'gentype_SimpleIndex));
# 344 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 42 "Parser.fsy"
                                          IndTrue(parseState.ResultRange) 
                   )
# 42 "Parser.fsy"
                 : 'gentype_SimpleIndex));
# 354 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Index in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 44 "Parser.fsy"
                                         _1 
                   )
# 44 "Parser.fsy"
                 : Index));
# 365 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_SimpleIndex in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 46 "Parser.fsy"
                                           _1 
                   )
# 46 "Parser.fsy"
                 : 'gentype_Index));
# 376 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> 'gentype_IndAppList in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 47 "Parser.fsy"
                                                        _2 
                   )
# 47 "Parser.fsy"
                 : 'gentype_Index));
|]
# 388 "Parser.fs"
let tables : FSharp.Text.Parsing.Tables<_> = 
  { reductions = _fsyacc_reductions.Value;
    endOfInputTag = _fsyacc_endOfInputTag;
    tagOfToken = tagOfToken;
    dataOfToken = _fsyacc_dataOfToken; 
    actionTableElements = _fsyacc_actionTableElements;
    actionTableRowOffsets = _fsyacc_actionTableRowOffsets;
    stateToProdIdxsTableElements = _fsyacc_stateToProdIdxsTableElements;
    stateToProdIdxsTableRowOffsets = _fsyacc_stateToProdIdxsTableRowOffsets;
    reductionSymbolCounts = _fsyacc_reductionSymbolCounts;
    immediateActions = _fsyacc_immediateActions;
    gotos = _fsyacc_gotos;
    sparseGotoTableRowOffsets = _fsyacc_sparseGotoTableRowOffsets;
    tagOfErrorTerminal = _fsyacc_tagOfErrorTerminal;
    parseError = (fun (ctxt:FSharp.Text.Parsing.ParseErrorContext<_>) -> 
                              match parse_error_rich with 
                              | Some f -> f ctxt
                              | None -> parse_error ctxt.Message);
    numTerminals = 27;
    productionToNonTerminalTable = _fsyacc_productionToNonTerminalTable  }
let engine lexer lexbuf startState = tables.Interpret(lexer, lexbuf, startState)
let index lexer lexbuf : Index =
    engine lexer lexbuf 0 :?> _
let sort lexer lexbuf : Sort =
    engine lexer lexbuf 2 :?> _
