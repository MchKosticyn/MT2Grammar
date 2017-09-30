namespace MT

module internal MTTypes =
    type letterOfAlphabet = char
    type exSymbol = char
    type state = int
    type trackSymbol = TLetter of letterOfAlphabet | ExSymbol of exSymbol
    type Move = Right | Left
    type deltaFunc = Map<state * trackSymbol, state * trackSymbol * Move>
    type MT = state Set * letterOfAlphabet Set * trackSymbol Set * deltaFunc * state * state Set

module internal GrammarZeroTypes =
    open MTTypes

    type ExAplha = Letter of letterOfAlphabet | Eps
    type axiom = char
    type notNumedSymb = ExAplha * trackSymbol
    type var = NumSymb of int | State of state | Axiom of axiom
    type terminal = letterOfAlphabet
    type symbol = Var of var | Terminal of terminal | E
    type production = symbol list * symbol list
    type Grammar = var Set * letterOfAlphabet Set * production Set * axiom

module public FunctionalHelpers =
    let mapConcat f = List.concat << Set.map f

module internal Primitives =
    open MTTypes
    open GrammarZeroTypes

    let InitSymb = ExSymbol 'C'
    let EndSymb = ExSymbol '$'
    let mkState = State >> Var
    let mkAxiom = Axiom >> Var
    let inline tupleSymbol x y = (x, y)
    let Blank = ExSymbol 'B'
    let inline mkProduction left right = (left, right)
    let mkExAlphabet = Set.add Eps << Set.map Letter
    let mkTerminal = function
        | Letter x -> Terminal x
        | Eps -> E

module internal HelpFunctions =
    open MTTypes
    open GrammarZeroTypes

    let Coroutine2 lambda x y =
        seq { for a in x do
              for b in y do
                  yield lambda a b }

    let Coroutine3 lambda x y z =
        seq { for a in x do
              for b in y do
              for c in z do
                  yield lambda a b c }

    let fromSymbolToVar =
        Set.map (function
            | Var x -> x
            | _ -> failwith "not a variable")

    let enumerate = Seq.mapi (fun i x -> Var <| NumSymb i, x)

    let mapOfSymb c = Map.filter (fun _ -> snd >> (=) c)

    let toNumed tuple = Map.findKey (fun _ -> (=) tuple)

    let getNums = Map.toSeq >> Seq.map fst >> Set.ofSeq

    let getEqualPairs = Map.filter (fun _ -> function (Letter x, TLetter y) -> x = y | _ -> false)

module internal MTToGrammarZero =
    open HelpFunctions
    open Primitives
    open FunctionalHelpers
    open MTTypes
    open GrammarZeroTypes

    let transformation ((states, alphabet, tapeAlph, delta, initialState, finalStates) : MT) : Grammar =
        let allTuples = Coroutine2 tupleSymbol in
        let exAlph = mkExAlphabet alphabet in
        let AllTuplesMap : Map<symbol, notNumedSymb> = Map.ofSeq <| enumerate (allTuples exAlph tapeAlph) in
        let Variables : Set<var> =
            Set.union (fromSymbolToVar <| getNums AllTuplesMap) (Set.map State states)
            |> Set.add (Axiom 'A')
            |> Set.add (Axiom 'B')
            |> Set.add (Axiom 'C')
        in
        let firstPhase =
            let axiomA = mkAxiom 'A' in
            let axiomB = mkAxiom 'B' in
            let axiomC = mkAxiom 'C' in
            set [
                mkProduction [axiomA] [mkState initialState; axiomB];
                mkProduction [axiomB] [axiomC];
                mkProduction [axiomC] [toNumed (tupleSymbol Eps Blank) AllTuplesMap; axiomC];
                mkProduction [axiomC] [E]
            ]
            |> Set.union (Set.map (fun equalPair -> mkProduction [axiomB] [equalPair; axiomB]) (getNums <| getEqualPairs AllTuplesMap))
        in
        let secondPhase =
            let deltaStepToProductions (state, symbol) (newState, newSymbol, shift) =
                let shiftRight = Coroutine2 (fun a b   -> mkProduction [mkState state;a] [b;mkState newState])
                let shiftLeft  = Coroutine3 (fun a b c -> mkProduction [a;mkState state;b] [mkState newState;a;c])
                let numOfMapOldSymb = getNums <| mapOfSymb symbol AllTuplesMap
                let numOfMapNewSymb = getNums <| mapOfSymb newSymbol AllTuplesMap
                match shift with
                | Right -> shiftRight
                | Left  -> shiftLeft <| getNums AllTuplesMap
                <| numOfMapOldSymb
                <| numOfMapNewSymb
                |> Set.ofSeq
            Map.fold (fun acc k v -> Set.union acc <| deltaStepToProductions k v) Set.empty delta
        in
        let thirdPhase =
            Set.ofList <|
            Map.fold (fun acc k (a, _) ->
                mapConcat (fun state ->
                    let q = mkState state
                    let t = mkTerminal a
                    [
                        mkProduction [k; q] [q; t; q]
                        mkProduction [q; k] [q; t; q]
                        mkProduction [q] [E]
                    ]) finalStates
                @ acc)
                []
                AllTuplesMap
        in
        let prod = Set.unionMany [firstPhase; secondPhase; thirdPhase] in
        (Variables, alphabet, prod, 'A')
