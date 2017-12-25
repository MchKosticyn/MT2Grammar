namespace MT
open System.IO
open Prelude
open MTTypes

module Main =
    let writeToFile file (str : string) =
        use streamWriter = new StreamWriter(file, false)
        streamWriter.Write(str)
    [<EntryPoint>]
    let main _ =
        // Proof that MT works right
//        List.init 50 (fun n -> n, System.Convert.ToString(n, 2))
//        |> List.iter (fun (n, bn) -> printfn "%2O %6O %5O" n bn (TestMT.runMT BuildMT.PrimesMT bn))

        zero |> MTToGrammarZero.takeWords 1 |> Set.map (join ";") |> join "\n" |> printfn "%O"
//        let one = LBAToGrammarOne.transformation BuildMT.PrimesLBA
//        writeToFile "grammarOne.txt" <| ToString.grammarToString one
//        one |> LBAToGrammarOne.getWord |> Prelude.toString |> printfn "%s"
        0
