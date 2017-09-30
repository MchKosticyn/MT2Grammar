namespace MT
open MTTypes

module internal LBATypes =
    type Cent = Cent
    type Dollar = Dollar
    type TrackSymbolLBA = TrackSymbol of trackSymbol | StartSym of Cent | EndSym of Dollar
    type LBA = state Set * letterOfAlphabet Set * TrackSymbolLBA Set * deltaFunc * state * state Set

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

    let cent = StartSym Cent
    let dollar = EndSym Dollar

    let mkPtrAtLeftAllBounds    q Xa = PtrAtLeftAllBounds(q, Xa)
    let mkPtrAtSymbAllBounds    q Xa = PtrAtSymbAllBounds(q, Xa)
    let mkPtrAtRightAllBounds   q Xa = PtrAtRightAllBounds(q, Xa)
    let mkPtrNoBounds           q Xa = PtrNoBounds(q, Xa)
    let mkPtrAtSymbRightBound   q Xa = PtrAtSymbRightBound(q, Xa)
    let mkPtrAtRightRightBound  q Xa = PtrAtRightRightBound(q, Xa)
    let mkPtrAtLeftLeftBound    q Xa = PtrAtLeftLeftBound(q, Xa)
    let mkPtrAtSymbLeftBound    q Xa = PtrAtSymbLeftBound(q, Xa)
    let mkProduction x y = (x, y)


module internal LBAToGrammarOne =
    open GrammarOnePrimitives
    open HelpFunctions
    open Primitives
    open LBATypes

    let transformationT1 ((states, alphabet, tapeAlph, delta, initialState, finalStates) : LBA) : Grammar =
        let tapeAlphNoBounds =
            Seq.choose (function | StartSym _ | EndSym _ -> None | TrackSymbol t -> Some t) tapeAlph
        let allVarAndVals = Coroutine2 tupleSymbol tapeAlphNoBounds alphabet

        let axiomA = RawNonTerminal 'A'
        let axiomB = RawNonTerminal 'B'

        let isFinite =
            function
            | PtrNoBounds(q, _)
            | PtrAtSymbRightBound(q, _)
            | PtrAtRightRightBound(q, _)
            | PtrAtLeftLeftBound(q, _)
            | PtrAtSymbLeftBound(q, _) -> Set.contains q finalStates

        let allPtrAtLeftAllBounds   = Set.ofSeq <| Coroutine2 mkPtrAtLeftAllBounds   states allVarAndVals
        let allPtrAtSymbAllBounds   = Set.ofSeq <| Coroutine2 mkPtrAtSymbAllBounds   states allVarAndVals
        let allPtrAtRightAllBounds  = Set.ofSeq <| Coroutine2 mkPtrAtRightAllBounds  states allVarAndVals
        let allPtrNoBounds          = Set.ofSeq <| Coroutine2 mkPtrNoBounds          states allVarAndVals
        let allPtrAtSymbRightBound  = Set.ofSeq <| Coroutine2 mkPtrAtSymbRightBound  states allVarAndVals
        let allPtrAtRightRightBound = Set.ofSeq <| Coroutine2 mkPtrAtRightRightBound states allVarAndVals
        let allPtrAtLeftLeftBound   = Set.ofSeq <| Coroutine2 mkPtrAtLeftLeftBound   states allVarAndVals
        let allPtrAtSymbLeftBound   = Set.ofSeq <| Coroutine2 mkPtrAtSymbLeftBound   states allVarAndVals

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

        let cntToSymb = CompoundNonTerminal >> NonTerminal

        let Step1 =
            Set.map (fun a -> mkProduction [axiomA] [PtrAtLeftAllBounds(initialState, (TLetter a, a))]) alphabet

//        let prod = List.map
//            (fun vlvr -> mkProduction [RawNonTerminal 'A'] [mkPtrAtLeftAllBounds initialState vlvr])
//            (Seq.zip alphabet alphabet)

        (nonTerminals, alphabet, set[], 'A')
