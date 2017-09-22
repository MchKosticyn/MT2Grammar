module MT.ToGrammar
// types : MT
type letterOfAlphabet = char
type exSymbol = char
type state = int
type trackSymbol = TLetter of letterOfAlphabet | ExSymbol of exSymbol
type Move = Right | Left
type deltaFunc = Map<state * trackSymbol, state * trackSymbol * Move>
type MT = state Set * letterOfAlphabet Set * trackSymbol Set * deltaFunc * state * state Set

// types : Grammar
type ExAplha = Letter of letterOfAlphabet | Eps
type axiom = char
type notNumedSymb = ExAplha * trackSymbol
type var = NumSymb of int | State of state | Axiom of axiom
type terminal = letterOfAlphabet
type symbol = Var of var | Terminal of terminal | E
type production = symbol list * symbol list
type Grammar = var Set * letterOfAlphabet Set * production Set * axiom

// Functional helpers
let rec mapConcat f = List.concat << List.map f

// Primitives
let inline mkState state = Var <| State state
let inline mkAxiom axiom = Var <| Axiom axiom
let inline tupleSymbol x y = (x, y)
let Blank = ExSymbol 'B'
let inline mkProduction left right = (left, right)
let mkExAlphabet alpha = Set.add Eps <| Set.map Letter alpha
let mkTerminal = function
        | Letter x -> Terminal x
        | Eps -> E

// Help functions
let Coroutine2 lambda x y =
    seq { for a in x do
          for b in y do
              yield lambda a b }

let Coroutine3 lambda x y z =
    seq { for a in x do
          for b in y do
          for c in z do
              yield lambda a b c }

let allTuples exAlphabet tapeAlphabet = List.ofSeq <| Coroutine2 (fun a b -> tupleSymbol a b) exAlphabet tapeAlphabet

let fromSymbolToVar =
    Set.map (function
        | Var x -> x
        | _ -> failwith "not a variable")

let enumerate = List.mapi (fun i x -> Var <| NumSymb i, x)

let mapOfSymb c = Map.filter (fun k v ->
    match v with
    | (_, right) when right = c -> true
    | _ -> false)

let toNumed tuple mapa = Map.findKey (fun k v -> v = tuple) mapa

let getNums mapa = mapa |> Map.toSeq |> Seq.map fst |> Set.ofSeq

let getEqualPairs = Map.filter (fun k v ->
    match v with
    | (Letter x, TLetter y) when x = y -> true
    | _ -> false)

// Mutate
let transformation ((states, alphabet, tapeAlph, delta, initialState, finalStates) : MT) : Grammar =
    let exAlph = mkExAlphabet alphabet in
    let AllTuplesMap : Map<symbol, notNumedSymb> = Map.ofList <| enumerate (allTuples exAlph tapeAlph) in
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
        [mkProduction [axiomA] [mkState initialState; axiomB];
        mkProduction [axiomB] [axiomC];
        mkProduction [axiomC] [toNumed (tupleSymbol Eps Blank) AllTuplesMap; axiomC];
        mkProduction [axiomC] [E]]
        |> Set.ofList
        |> Set.union (Set.map (fun equalPair -> mkProduction [axiomB] [equalPair; axiomB]) (getNums <| getEqualPairs AllTuplesMap))
    in
    let secondPhase =
        Map.fold (fun acc (state, symbol) (newState, newSymbol, shift) ->
            let shiftRight set1 set2 = Set.ofSeq <| Coroutine2 (fun a b -> mkProduction [mkState state; a] [b;mkState newState]) set1 set2
            let shiftLeft set1 set2 set3 = Set.ofSeq <| Coroutine3 (fun a b c -> mkProduction [a;mkState state;b] [mkState newState;a;c]) set1 set2 set3
            match shift with
            | Right -> shiftRight (getNums <| mapOfSymb symbol AllTuplesMap) (getNums <| mapOfSymb newSymbol AllTuplesMap)
            | Left -> shiftLeft (getNums <| AllTuplesMap) (getNums <| mapOfSymb symbol AllTuplesMap) (getNums <| mapOfSymb newSymbol AllTuplesMap)
            |> Set.union acc)
            Set.empty
            delta
    in
    let thirdPhase =
        Set.ofList <|
        Map.fold (fun acc k (a, c) ->
            List.append acc <|
            mapConcat (fun state ->
                let sState = mkState state
                let t = mkTerminal a
                [mkProduction [k; sState] [mkState state; t; sState];
                mkProduction [k; sState] [mkState state; t; sState];
                mkProduction [k; sState] [mkState state; t; sState]]
                )
                (Set.toList <| finalStates))
            []
            AllTuplesMap
    in
    let prod = Set.unionMany [firstPhase; secondPhase; thirdPhase] in
    (Variables, alphabet, prod, 'A')
