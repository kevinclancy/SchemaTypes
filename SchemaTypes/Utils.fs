module Utils

open FSharp.Text.Lexing

let noRange = (Position.Empty, Position.Empty)

/// Returns a variable name derived from *seed* that does not occur in *freeVars*
let freshVar (freeVars : Set<string>) (seed : string) : string =
    // the seed's numeric suffix, if it has one, is where we start counting
    let seedStr, seedInt = 
        let prefix = seed.TrimEnd([| '0' .. '9' |])
        match prefix.Length < seed.Length with
        | true ->
            (prefix, System.Int32.Parse(seed.Substring(prefix.Length)))
        | false ->
            (seed, 0)
    let rec getSuffix (seedStr : string) (candidate : int) : int =
        match freeVars.Contains (seedStr + candidate.ToString()) with
        | true ->
            getSuffix seedStr (candidate + 1)
        | false ->
            candidate
    seedStr + (getSuffix seedStr seedInt).ToString()
