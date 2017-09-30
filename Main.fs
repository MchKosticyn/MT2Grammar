namespace MT
module Main =
    [<EntryPoint>]
    let main _ =
        MTToGrammarZero.transformation BuildMT.PrimesMT
        |> printfn "%A\n"
        0
