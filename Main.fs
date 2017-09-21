open MT

[<EntryPoint>]
let main _ =
    ToGrammar.transformation Lp.BuildMT.PrimesMT
    |> printfn "%A\n"
    0
