namespace MT
open Prelude
open MTTypes
open LBATypes

module Main =
    [<EntryPoint>]
    let main _ =
        // Proof that MT works right
//        List.init 50 (fun n -> n, System.Convert.ToString(n, 2))
//        |> List.iter (fun (n, bn) -> printfn "%2O %6O %5O" n bn (TestMT.runMT BuildMT.PrimesMT bn))

        // Proof that LBA works right
//        List.init 50 (fun n -> n, System.Convert.ToString(n, 2))
//        |> List.iter (fun (n, bn) -> printfn "%2O %6O %5O" n bn (TestMT.runLBA BuildMT.PrimesLBA bn))


//        let simpleMT : MT = set[0; 1], set['v'; 'k'], set[TLetter 'k'; TLetter 'v'; ExSymbol 'B'], Map.ofList[((0, TLetter 'v'), (1, TLetter 'v', Right))], 0, set[1]

//        let simpleLBA : LBA =
//            set[0; 1; 2; 3], set['v'; 'k'], set[TrackSymbol <| TLetter 'v'; TrackSymbol <| TLetter 'k'; TrackSymbol <| ExSymbol 'B'; StartSym Cent; EndSym Dollar],
//            Map.ofList[
//                ((0, StartSym Cent), (0, StartSym Cent, Right))
//                ((0, TrackSymbol <| TLetter 'v'), (1, TrackSymbol <| TLetter 'v', Right))
//                ((1, TrackSymbol <| ExSymbol 'B'), (2, TrackSymbol <| ExSymbol 'B', Right))
//                ((2, TrackSymbol <| TLetter 'k'), (3, TrackSymbol <| TLetter 'k', Right))
//            ],
//            0, set[3]

        printfn "Печать грамматики типа Т0 в файл..."
        let zero = MTToGrammarZero.transformation BuildMT.PrimesMT // simpleMT
        writeToFile "T0.Grammar.txt" <| ToString.grammarToString zero
        printfn "Печать закончена."
        printfn "Печать вывода простого числа в грамматике типа Т0..."
        zero |> MTToGrammarZero.takeWords 1 |> Set.map (join "") |> join "\n" |> printfn "Простое число (в бинарном формате): %O"
        printfn "Печать закончена.\n"

        printfn "Печать грамматики типа Т1 в файл..."
        let one = LBAToGrammarOne.transformation BuildMT.PrimesLBA
        writeToFile "T1.Grammar.txt" <| ToString.grammarToString one
        printfn "Печать закончена."
        printfn "Печать вывода простого числа в грамматике типа Т1..."
        one |> LBAToGrammarOne.takeWords 1 |> Set.map (join "") |> join "\n" |> printfn "Простое число (в бинарном формате): %O"
        printfn "Печать закончена."

        0
