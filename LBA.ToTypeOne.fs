namespace MT
open MTTypes
open System
open Prelude

module internal LBATypes =
    type Cent = Cent
    type Dollar = Dollar
    type TrackSymbolLBA = TrackSymbol of trackSymbol | StartSym of Cent | EndSym of Dollar
    type deltaFuncLBA = Map<state * TrackSymbolLBA, state * TrackSymbolLBA * Move>
    type LBA = state Set * letterOfAlphabet Set * TrackSymbolLBA Set * deltaFuncLBA * state * state Set

module internal GrammarOneTypes =
    type axiom = char
    type VarAndVal = trackSymbol * letterOfAlphabet
    type CompoundNonTerminal =
        | PtrAtLeftAllBounds    of state * VarAndVal  // [q, ¢, X, a, $]
        | PtrAtSymbAllBounds    of state * VarAndVal  // [¢, q, X, a, $]
        | PtrAtRightAllBounds   of state * VarAndVal  // [¢, X, a, q, $]
        | PtrNoBounds           of state * VarAndVal  // [q, X, a]
        | PtrAtSymbRightBound   of state * VarAndVal  // [q, X, a, $]
        | PtrAtRightRightBound  of state * VarAndVal  // [X, a, q, $]
        | LeftBoundAndSymb      of VarAndVal          // [¢, X, a]
        | VarAndVal             of VarAndVal          // [X, a]
        | RightBoundAndSymb     of VarAndVal          // [X, a, $]
        | PtrAtLeftLeftBound    of state * VarAndVal  // [q, ¢, X, a]
        | PtrAtSymbLeftBound    of state * VarAndVal  // [¢, q, X, a]
        with
        override this.ToString() =
            let vavToString = function
                | (TLetter x, y) -> (x, y)
                | (ExSymbol x, y) -> (x, y)
            match this with
            | PtrAtLeftAllBounds    (st, vav) -> sprintf "[%O, ¢, %O, $]" st <| vavToString vav
            | PtrAtSymbAllBounds    (st, vav) -> sprintf "[¢, %O, %O, $]" st <| vavToString vav
            | PtrAtRightAllBounds   (st, vav) -> sprintf "[¢, %O, %O, $]" st <| vavToString vav
            | PtrNoBounds           (st, vav) -> sprintf "[%O, %O]" st <| vavToString vav
            | PtrAtSymbRightBound   (st, vav) -> sprintf "[%O, %O, $]" st <| vavToString vav
            | PtrAtRightRightBound  (st, vav) -> sprintf "[%O, %O, $]" st <| vavToString vav
            | LeftBoundAndSymb            vav -> sprintf "[¢, %O]" <| vavToString vav
            | VarAndVal                   vav -> sprintf "[%O]" <| vavToString vav
            | RightBoundAndSymb           vav -> sprintf "[%O, $]" <| vavToString vav
            | PtrAtLeftLeftBound    (st, vav) -> sprintf "[%O, ¢, %O]" st <| vavToString vav
            | PtrAtSymbLeftBound    (st, vav) -> sprintf "[¢, %O, %O]" st <| vavToString vav
    type NonTerminal =
        | RawNonTerminal of axiom
        | CompoundNonTerminal of CompoundNonTerminal
        | NumedNonTerminal of int
        with
        override this.ToString() =
            match this with
            | RawNonTerminal x -> toString x
            | NumedNonTerminal x -> "NT" + toString x
            | CompoundNonTerminal x -> toString x //failwithf "internal error: wrong non-terminal!"
    type terminal = letterOfAlphabet
    type symbol =
        | NonTerminal of NonTerminal
        | Terminal of terminal
        with
        override this.ToString() =
            match this with
            | NonTerminal x -> toString x
            | Terminal x -> toString x
    type production = symbol list * symbol list
    type Grammar = NonTerminal Set * terminal Set * production Set * axiom

module internal GrammarOnePrimitives =
    open LBATypes
    open GrammarOneTypes

    let axiomA = RawNonTerminal 'A'
    let axiomB = RawNonTerminal 'B'
    let ntAxiomA = NonTerminal axiomA
    let ntAxiomB = NonTerminal axiomB
    let cent = StartSym Cent
    let dollar = EndSym Dollar
    let cntToSymb = CompoundNonTerminal >> NonTerminal

    let inline mkProductionRaw x y = (x, y)
    let inline mkProduction x y = mkProductionRaw (List.map cntToSymb x) (List.map cntToSymb y)
    let inline tupleSymbol x y = (x, y)

    let getVarAndVal =
        function
        | PtrAtLeftAllBounds    (_, Xa)
        | PtrAtSymbAllBounds    (_, Xa)
        | PtrAtRightAllBounds   (_, Xa)
        | PtrNoBounds           (_, Xa)
        | PtrAtSymbRightBound   (_, Xa)
        | PtrAtRightRightBound  (_, Xa)
        | LeftBoundAndSymb      Xa
        | VarAndVal             Xa
        | RightBoundAndSymb     Xa
        | PtrAtLeftLeftBound    (_, Xa)
        | PtrAtSymbLeftBound    (_, Xa) -> Xa
    let getTerminalFromCnt = getVarAndVal >> snd >> Terminal

module internal LBAToGrammarOne =
    open System.Collections.Generic
    open GrammarOnePrimitives
    open GrammarOneTypes
    open HelpFunctions
    open LBATypes

    let takeWords n ((_, _, prods, axiom): Grammar) =
        let exchange word left right =
            let rec echange_help prefix word =
                let compare word =
                    let rec help word left =
                        match word, left with
                        | _, [] -> Some <| List.rev prefix @ right @ word
                        | x::xs, y::ys when x = y -> help xs ys
                        | _ -> None
                    help word left

                if List.length word < List.length left
                then set[]
                else
                    match word with
                    | hd::tl -> Option.foldBack Set.add (compare word) <| echange_help (hd::prefix) tl
            echange_help [] word

        let printWord = Prelude.writeToFile "T1.Formation.txt" << sprintf "%s\n" << Prelude.join " "

        let allTerminals = List.forall (function Terminal _ -> true | _ -> false)
        let q = Queue<symbol list>()
        let mutable allRes : Set<symbol list> = set[]
        let mutable res =
            List.replicate (2 * 3 + 3) 6297
            |> List.append [6279; 3140; 6290; 6290]
            |> List.map (NumedNonTerminal >> NonTerminal) // simpleLBA: [332; 309; 316]
        printWord [NonTerminal <| RawNonTerminal axiom]
        printWord res
        while Set.count allRes < n do
            Set.iter (fun (left, right) ->
                let words = exchange res left right
                if not(Set.isEmpty words) then
                    let terminalWords, nonterminalWords = Set.partition allTerminals words
                    allRes <- Set.union terminalWords allRes
                    let nonterminalWords = Set.remove res nonterminalWords
                    let nonterminalWords = Set.filter (not << q.Contains) nonterminalWords
                    Set.iter q.Enqueue nonterminalWords) prods
            if q.Count <> 0 then
                res <- q.Dequeue()
            printWord res
        Set.map (List.filter ((<>) <| Terminal '\000')) allRes

    let transformation ((states, alphabet, tapeAlph, delta, initialState, finalStates) : LBA) : Grammar =
        let alphabet = Set.add '\000' alphabet
        let fromTrackSymbLBA = function
            | TrackSymbol symb -> symb
            | StartSym Cent -> ExSymbol 'C'
            | EndSym Dollar -> ExSymbol '$'

        let tapeAlphNoBounds =
            Seq.choose (function StartSym _ | EndSym _ -> None | TrackSymbol t -> Some t) tapeAlph
            |> Seq.append [TLetter '\000']
        let allVarAndVals =
            Coroutine2 tapeAlphNoBounds alphabet makePair
            |> Set.ofSeq

        let isFinite =
            function
            | PtrAtLeftAllBounds    (q, _)
            | PtrAtSymbAllBounds    (q, _)
            | PtrAtRightAllBounds   (q, _)
            | PtrNoBounds           (q, _)
            | PtrAtSymbRightBound   (q, _)
            | PtrAtRightRightBound  (q, _)
            | PtrAtLeftLeftBound    (q, _)
            | PtrAtSymbLeftBound    (q, _) -> Set.contains q finalStates
            | _ -> false


        let generateAllNonterminals p = Set.ofSeq <| Coroutine2 states allVarAndVals (fun q Xa -> p(q, Xa))
        let allPtrAtLeftAllBounds   = generateAllNonterminals PtrAtLeftAllBounds
        let allPtrAtSymbAllBounds   = generateAllNonterminals PtrAtSymbAllBounds
        let allPtrAtRightAllBounds  = generateAllNonterminals PtrAtRightAllBounds
        let allPtrNoBounds          = generateAllNonterminals PtrNoBounds
        let allPtrAtSymbRightBound  = generateAllNonterminals PtrAtSymbRightBound
        let allPtrAtRightRightBound = generateAllNonterminals PtrAtRightRightBound
        let allPtrAtLeftLeftBound   = generateAllNonterminals PtrAtLeftLeftBound
        let allPtrAtSymbLeftBound   = generateAllNonterminals PtrAtSymbLeftBound

        let allLeftBoundAndSymb  = Set.ofSeq <| Seq.map LeftBoundAndSymb  allVarAndVals
        let allVarAndVal         = Set.ofSeq <| Seq.map VarAndVal         allVarAndVals
        let allRightBoundAndSymb = Set.ofSeq <| Seq.map RightBoundAndSymb allVarAndVals

        let allNonTerminals =
            [
                allPtrAtLeftAllBounds
                allPtrAtSymbAllBounds
                allPtrAtRightAllBounds
                allPtrNoBounds
                allPtrAtSymbRightBound
                allPtrAtRightRightBound
                allPtrAtLeftLeftBound
                allPtrAtSymbLeftBound
                allLeftBoundAndSymb
                allVarAndVal
                allRightBoundAndSymb
            ]
            |> Set.unionMany
            |> Set.map CompoundNonTerminal

        let numedNonTerminals = Map.ofList <| List.mapi (fun i x -> x, i) (List.ofSeq allNonTerminals)

        let opWithDelta =
            let deltaStep (state, symbol) (newState, newSymbol, shift) =
                let symb = fromTrackSymbLBA symbol
                let newSymb = fromTrackSymbLBA newSymbol
                let shiftLeft : seq<production> =
                    Seq.collect (fun a ->
                        let stateAndSymb = (state, (symb, a))
                        let newSymb = (newSymb, a)
                        Seq.collect (fun Zb ->
                            [
                                mkProduction [VarAndVal Zb; PtrNoBounds stateAndSymb] [PtrNoBounds(newState, Zb); VarAndVal newSymb]; // 6.2
                                mkProduction [LeftBoundAndSymb Zb; PtrNoBounds stateAndSymb] [PtrAtSymbLeftBound(newState, Zb); VarAndVal newSymb] // my
                                mkProduction [VarAndVal Zb; PtrAtSymbRightBound stateAndSymb] [PtrNoBounds(newState, Zb); RightBoundAndSymb newSymb] // 7.3
                                mkProduction [LeftBoundAndSymb Zb; PtrAtSymbRightBound stateAndSymb] [PtrAtSymbLeftBound(newState, Zb); RightBoundAndSymb newSymb] // my
                            ])
                            allVarAndVals
                        |> Seq.append <|
                        [
                            mkProduction [PtrAtSymbAllBounds stateAndSymb] [PtrAtLeftAllBounds(newState, newSymb)]; // 2.2
                            mkProduction [PtrAtSymbLeftBound stateAndSymb] [PtrAtLeftLeftBound(newState, newSymb)] // 5.2
                        ])
                        alphabet

                let shiftLeftDollar =
                    Seq.collect (fun Xa ->
                        [
                            mkProduction [PtrAtRightAllBounds(state, Xa)] [PtrAtSymbAllBounds(newState, Xa)]; // 2.4
                            mkProduction [PtrAtRightRightBound(state, Xa)] [PtrAtSymbRightBound(newState, Xa)] // 7.2
                        ])
                        allVarAndVals

                let shiftRight : seq<production> =
                    Seq.collect (fun a ->
                        Seq.collect (fun Zb ->
                            [
                                mkProduction [PtrAtSymbLeftBound(state, (symb, a)); VarAndVal Zb] [LeftBoundAndSymb(newSymb, a); PtrNoBounds(newState, Zb)]; // 5.3
                                mkProduction [PtrAtSymbLeftBound(state, (symb, a)); RightBoundAndSymb Zb] [LeftBoundAndSymb(newSymb, a); PtrAtSymbRightBound(newState, Zb)] // my
                                mkProduction [PtrNoBounds(state, (symb, a)); VarAndVal Zb] [VarAndVal(newSymb, a); PtrNoBounds(newState, Zb)] // 6.1
                                mkProduction [PtrNoBounds(state, (symb, a)); RightBoundAndSymb Zb] [VarAndVal(newSymb, a); PtrAtSymbRightBound(newState, Zb)] // 6.3
                            ])
                            allVarAndVals
                        |> Seq.append <|
                        [
                            mkProduction [PtrAtSymbAllBounds(state, (symb, a))] [PtrAtRightAllBounds(newState, (newSymb, a))]; // 2.3
                            mkProduction [PtrAtSymbRightBound(state, (symb, a))] [PtrAtRightRightBound(newState, (newSymb, a))] // 7.1
                        ])
                        alphabet

                let shiftRightCent : seq<production> =
                    Seq.collect (fun Xa ->
                        [
                            mkProduction [PtrAtLeftAllBounds(state, Xa)] [PtrAtSymbAllBounds(newState, Xa)]; // 2.1
                            mkProduction [PtrAtLeftLeftBound(state, Xa)] [PtrAtSymbLeftBound(newState, Xa)] // 5.1
                        ])
                        allVarAndVals

                match shift, symbol, newSymbol with
                | Right, x, y when x = y && x = cent -> shiftRightCent
                | Left, x, y when x = y && x = dollar -> shiftLeftDollar
                | _, x, y when x = cent || y = cent || x = dollar || y = dollar -> Seq.empty
                | Left, _, _ -> shiftLeft
                | Right, _, _ -> shiftRight
                |> Set.ofSeq
            Map.fold (fun acc k v -> Set.union acc <| deltaStep k v) Set.empty delta

        let Step1 : Set<production> =
            Set.map (fun a -> mkProductionRaw [ntAxiomA] [cntToSymb <| PtrAtLeftAllBounds(initialState, (TLetter a, a))]) alphabet

        let Step3 : Set<production> =
            Coroutine2 finalStates allVarAndVals
                (fun q Xa ->
                    [PtrAtLeftAllBounds; PtrAtSymbAllBounds; PtrAtRightAllBounds]
                    |> List.map (fun p -> mkProductionRaw [cntToSymb <| p(q, Xa)] [Terminal <| snd Xa])
                    |> Set.ofList)
            |> Set.unionMany

        let Step4 : Set<production> =
            Set.map
                (fun a ->
                    let aa = (TLetter a, a)
                    set [mkProductionRaw [ntAxiomA] [cntToSymb <| PtrAtLeftLeftBound(initialState, aa); ntAxiomB]
                         mkProductionRaw [ntAxiomB] [cntToSymb <| VarAndVal(aa); ntAxiomB]
                         mkProductionRaw [ntAxiomB] [cntToSymb <| RightBoundAndSymb(aa)]])
                alphabet
            |> Set.unionMany

        let Step8 : Set<production> =
            [
                allPtrNoBounds // 8.3
                allPtrAtSymbRightBound // 8.4
                allPtrAtRightRightBound // 8.5
                allPtrAtLeftLeftBound // 8.1
                allPtrAtSymbLeftBound // 8.2
            ] |> Set.unionMany
            |> Set.filter isFinite
            |> Set.map (fun cnt -> mkProductionRaw [cntToSymb cnt] [getTerminalFromCnt cnt])

        let Step9 : Set<production> =
            let St9Dot12 =
                Coroutine2 alphabet (allVarAndVal + allRightBoundAndSymb)
                    (fun a cnt -> mkProductionRaw [Terminal a; cntToSymb cnt]
                                                  [Terminal a; getTerminalFromCnt cnt])
            let St9Dot34 =
                Coroutine2 alphabet (allVarAndVal + allLeftBoundAndSymb)
                    (fun b cnt -> mkProductionRaw [cntToSymb cnt; Terminal b]
                                                  [getTerminalFromCnt cnt; Terminal b])

            Set.ofSeq <| Seq.append St9Dot12 St9Dot34

        let productions =
            Set.unionMany [Step1; Step3; Step4; Step8; Step9; opWithDelta]

        let enumerateProd = List.map (function
            | NonTerminal (CompoundNonTerminal _ as symb) -> Map.find symb numedNonTerminals |> NumedNonTerminal |> NonTerminal
            | symb -> symb)

        let numedProductions = Set.map (fun (leftProd, rightProd) -> enumerateProd leftProd, enumerateProd rightProd) productions

        let nonTerminalsNums = numedNonTerminals |> Map.fold (fun acc _ v -> Set.add (NumedNonTerminal v) acc) Set.empty

        (nonTerminalsNums, alphabet, numedProductions, 'A')
