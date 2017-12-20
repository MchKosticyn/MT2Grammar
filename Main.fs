namespace MT
open System.IO
module Main =
    let writeToFile file (str : string) =
        use streamWriter = new StreamWriter(file, false)
        streamWriter.Write(str)
    [<EntryPoint>]
    let main _ =
        let zero = MTToGrammarZero.transformation BuildMT.PrimesMT
        writeToFile "grammarZero.txt" <| ToString.grammarToString zero
        zero |> MTToGrammarZero.getWord |> Prelude.toString |> printfn "%s"
        let one = LBAToGrammarOne.transformation BuildMT.PrimesLBA
        writeToFile "grammarOne.txt" <| ToString.grammarToString one
        one |> LBAToGrammarOne.getWord |> Prelude.toString |> printfn "%s"
        0
