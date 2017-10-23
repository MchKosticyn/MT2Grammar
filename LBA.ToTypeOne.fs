namespace MT
open MTTypes

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
    type NonTerminal =
        | RawNonTerminal of axiom
        | CompoundNonTerminal of CompoundNonTerminal
    type terminal = letterOfAlphabet
    type symbol = NonTerminal of NonTerminal | Terminal of terminal
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

    let mkProduction x y = (x, y)

    let cntToSymb = CompoundNonTerminal >> NonTerminal

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
    open GrammarOnePrimitives
    open GrammarOneTypes
    open HelpFunctions
    open Primitives
    open LBATypes

    let transformationT1 ((states, alphabet, tapeAlph, delta, initialState, finalStates) : LBA) : Grammar =
        let fromTrackSymbLBA = function
            | TrackSymbol symb -> symb
            | StartSym Cent -> ExSymbol 'C'
            | EndSym Dollar -> ExSymbol '$'

        let tapeAlphNoBounds =
            Seq.choose (function | StartSym _ | EndSym _ -> None | TrackSymbol t -> Some t) tapeAlph
        let allVarAndVals = Coroutine2 tupleSymbol tapeAlphNoBounds alphabet

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


        let allPtrAtLeftAllBounds   = Set.ofSeq <| Coroutine2 (fun q Xa -> PtrAtLeftAllBounds(q, Xa))   states allVarAndVals
        let allPtrAtSymbAllBounds   = Set.ofSeq <| Coroutine2 (fun q Xa -> PtrAtSymbAllBounds(q, Xa))   states allVarAndVals
        let allPtrAtRightAllBounds  = Set.ofSeq <| Coroutine2 (fun q Xa -> PtrAtRightAllBounds(q, Xa))  states allVarAndVals
        let allPtrNoBounds          = Set.ofSeq <| Coroutine2 (fun q Xa -> PtrNoBounds(q, Xa))          states allVarAndVals
        let allPtrAtSymbRightBound  = Set.ofSeq <| Coroutine2 (fun q Xa -> PtrAtSymbRightBound(q, Xa))  states allVarAndVals
        let allPtrAtRightRightBound = Set.ofSeq <| Coroutine2 (fun q Xa -> PtrAtRightRightBound(q, Xa)) states allVarAndVals
        let allPtrAtLeftLeftBound   = Set.ofSeq <| Coroutine2 (fun q Xa -> PtrAtLeftLeftBound(q, Xa))   states allVarAndVals
        let allPtrAtSymbLeftBound   = Set.ofSeq <| Coroutine2 (fun q Xa -> PtrAtSymbLeftBound(q, Xa))   states allVarAndVals

        let allLeftBoundAndSymb  = Set.ofSeq <| Seq.map LeftBoundAndSymb  allVarAndVals
        let allVarAndVal         = Set.ofSeq <| Seq.map VarAndVal         allVarAndVals
        let allRightBoundAndSymb = Set.ofSeq <| Seq.map RightBoundAndSymb allVarAndVals

        let nonTerminals : Set<NonTerminal> =
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
            allNonTerminals
            |> Set.add axiomA
            |> Set.add axiomB

        let opWithDelta =
            let deltaStep (state, symbol) (newState, newSymbol, shift) =
                let symb = fromTrackSymbLBA symbol
                let newSymb = fromTrackSymbLBA newSymbol
                let shiftLeft : seq<production> =
                    Seq.collect (fun a ->
                        Seq.collect (fun Zb ->
                            [
                                mkProduction [cntToSymb <| VarAndVal Zb; cntToSymb <| PtrNoBounds(state, (symb, a))] [cntToSymb <| PtrNoBounds(newState, Zb); cntToSymb <| VarAndVal(newSymb, a)];
                                mkProduction [cntToSymb <| VarAndVal Zb; cntToSymb <| PtrAtSymbRightBound(state, (symb, a))] [cntToSymb <| PtrNoBounds(newState, Zb); cntToSymb <| RightBoundAndSymb(newSymb, a)]
                            ])
                            allVarAndVals
                        |> Seq.append <|
                        [
                            mkProduction [cntToSymb <| PtrAtSymbAllBounds(state, (symb, a))] [cntToSymb <| PtrAtLeftAllBounds(newState, (newSymb, a))];
                            mkProduction [cntToSymb <| PtrAtSymbLeftBound(state, (symb, a))] [cntToSymb <| PtrAtLeftLeftBound(newState, (newSymb, a))]
                        ])
                        alphabet

                let shiftLeftDollar =
                    Seq.collect (fun Xa ->
                        [
                            mkProduction [cntToSymb <| PtrAtRightAllBounds(state, Xa)] [cntToSymb <| PtrAtSymbAllBounds(newState, Xa)];
                            mkProduction [cntToSymb <| PtrAtRightRightBound(state, Xa)] [cntToSymb <| PtrAtSymbRightBound(newState, Xa)]
                        ])
                        allVarAndVals

                let shiftRight : seq<production> =
                    Seq.collect (fun a ->
                        Seq.collect (fun Zb ->
                            [
                                mkProduction [cntToSymb <| PtrAtSymbLeftBound(state, (symb, a)); cntToSymb <| VarAndVal Zb] [cntToSymb <| LeftBoundAndSymb(newSymb, a); cntToSymb <| PtrNoBounds(newState, Zb)];
                                mkProduction [cntToSymb <| PtrNoBounds(state, (symb, a)); cntToSymb <| VarAndVal Zb] [cntToSymb <| VarAndVal(newSymb, a); cntToSymb <| PtrNoBounds(newState, Zb)]
                                mkProduction [cntToSymb <| PtrNoBounds(state, (symb, a)); cntToSymb <| RightBoundAndSymb Zb] [cntToSymb <| VarAndVal(newSymb, a); cntToSymb <| PtrAtSymbRightBound(newState, Zb)]
                            ])
                            allVarAndVals
                        |> Seq.append <|
                        [
                            mkProduction [cntToSymb <| PtrAtSymbAllBounds(state, (symb, a))] [cntToSymb <| PtrAtRightAllBounds(newState, (newSymb, a))];
                            mkProduction [cntToSymb <| PtrAtSymbRightBound(state, (symb, a))] [cntToSymb <| PtrAtRightRightBound(newState, (newSymb, a))]
                        ])
                        alphabet

                let shiftRightCent : seq<production> =
                    Seq.collect (fun Xa ->
                        [
                            mkProduction [cntToSymb <| PtrAtLeftAllBounds(state, Xa)] [cntToSymb <| PtrAtSymbAllBounds(newState, Xa)];
                            mkProduction [cntToSymb <| PtrAtLeftLeftBound(state, Xa)] [cntToSymb <| PtrAtSymbLeftBound(newState, Xa)]
                        ])
                        allVarAndVals

                match shift, symbol, newSymbol with
                | Right, x, y when x = y && x = cent -> shiftRightCent
                | Left, x, y when x = y && x = dollar -> shiftLeftDollar
                | Left, _, _ -> shiftLeft
                | Right, _, _ -> shiftRight
                |> Set.ofSeq
            Map.fold (fun acc k v -> Set.union acc <| deltaStep k v) Set.empty delta

        let Step1 : Set<production> =
            Set.map (fun a -> mkProduction [ntAxiomA] [cntToSymb <| PtrAtLeftAllBounds(initialState, (TLetter a, a))]) alphabet

        let Step3 : Set<production> =
            Coroutine2
                (fun q Xa ->
                    [PtrAtLeftAllBounds; PtrAtSymbAllBounds; PtrAtRightAllBounds]
                    |> List.map (fun p -> mkProduction [cntToSymb <| p(q, Xa)] [Terminal <| snd Xa])
                    |> Set.ofList)
                finalStates allVarAndVals
            |> Set.unionMany

        let Step4 : Set<production> =
            Set.map
                (fun a ->
                    let aa = (TLetter a, a)
                    set [mkProduction [ntAxiomA] [cntToSymb <| PtrAtLeftLeftBound(initialState, aa); ntAxiomB]
                         mkProduction [ntAxiomB] [cntToSymb <| VarAndVal(aa); ntAxiomB]
                         mkProduction [ntAxiomB] [cntToSymb <| RightBoundAndSymb(aa)]])
                alphabet
            |> Set.unionMany

        let Step8 : Set<production> =
            [
                allPtrNoBounds
                allPtrAtSymbRightBound
                allPtrAtRightRightBound
                allPtrAtLeftLeftBound
                allPtrAtSymbLeftBound
            ] |> Set.unionMany
            |> Set.filter isFinite
            |> Set.map (fun cnt -> mkProduction [cntToSymb cnt] [getTerminalFromCnt cnt])

        let Step9 : Set<production> =
            let St9Dot12 =
                Coroutine2
                    (fun a cnt -> mkProduction [Terminal a; cntToSymb cnt]
                                               [Terminal a; getTerminalFromCnt cnt])
                    alphabet <| allVarAndVal + allRightBoundAndSymb
            let St9Dot34 =
                Coroutine2
                    (fun b cnt -> mkProduction [cntToSymb cnt; Terminal b]
                                               [getTerminalFromCnt cnt; Terminal b])
                    alphabet <| allVarAndVal + allLeftBoundAndSymb

            Set.ofSeq <| Seq.append St9Dot12 St9Dot34

        let productions =
            Set.unionMany [Step1; Step3; Step4; Step8; Step9; opWithDelta]

        (nonTerminals, alphabet, productions, 'A')
