namespace MT
open System.IO
module Main =
    let writeToFile file (str : string) =
        use streamWriter = new StreamWriter(file, false)
        streamWriter.Write(str)
    [<EntryPoint>]
    let main _ =
        do MTToGrammarZero.transformation BuildMT.PrimesMT
        |> ToString.grammarToString
        |> writeToFile "grammarZero.txt"
        do LBAToGrammarOne.transformation BuildMT.PrimesLBA
        |> ToString.grammarToString
        |> writeToFile "grammarOne.txt"
        0
