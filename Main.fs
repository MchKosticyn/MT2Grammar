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

        let simpleMT : MT = set[0; 1], set['v'; 'k'], set[TLetter 'k'; TLetter 'v'; ExSymbol 'B'], Map.ofList[((0, TLetter 'v'), (1, TLetter 'v', Right))], 0, set[1]
        let zero = MTToGrammarZero.transformation BuildMT.PrimesMT//simpleMT
//        printfn "%O" <| (fun (_, _, exs, delta, start, fin) -> sprintf "%O\n%O\n%O" (exs |> (join ";")) delta fin) BuildMT.PrimesMT
        zero |> MTToGrammarZero.takeWords 1 |> Set.map (join "") |> join "\n" |> printfn "%O"
//        printfn "%O" <| ToString.grammarToString zero

//        let zero = MTToGrammarZero.transformation BuildMT.PrimesMT
//        writeToFile "grammarZero.txt" <| ToString.grammarToString zero
//        zero |> MTToGrammarZero.takeWords 1 |> Set.map (join ";") |> join "\n" |> printfn "%O"

//        let one = LBAToGrammarOne.transformation BuildMT.PrimesLBA
//        writeToFile "grammarOne.txt" <| ToString.grammarToString one
//        one |> LBAToGrammarOne.getWord |> Prelude.toString |> printfn "%s"
        0
