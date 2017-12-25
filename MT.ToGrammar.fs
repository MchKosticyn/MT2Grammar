namespace MT

module public Prelude =
    let toString x = x.ToString()
    let join s (xs: seq<'a>) = System.String.Join(s, xs)

module public ToString =
    open Prelude

    let productionToString (left, right) = sprintf "%O -> %O" (join " " left) (join " " right)
    let grammarToString (_, _, productions, axiom) =
        sprintf "Start non-terminal = %O\n%s" axiom <| join "\n" (Set.map productionToString productions)

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
    open Prelude

    type ExAplha = Letter of letterOfAlphabet | Eps
    type axiom = char
    type notNumedSymb = ExAplha * trackSymbol
    type var = NotNumedSymb of notNumedSymb | NumSymb of int | State of state | Axiom of axiom
        with
        override this.ToString() =
            match this with
            | NotNumedSymb _ -> failwith "wrong symb!"
            | NumSymb x -> "NT" + toString x
            | State x -> "ST" + toString x
            | Axiom x -> toString x
    type terminal = letterOfAlphabet
    type symbol = Var of var | Terminal of terminal | E
        with
        override this.ToString() =
            match this with
            | Var x -> toString x
            | Terminal x -> toString x
            | E -> ""
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
    let inline tupleSymbol x y = Var <| NotNumedSymb (x, y)
    let Blank = ExSymbol 'B'
    let inline mkProduction left right = (left, right)
    let mkExAlphabet = Set.add Eps << Set.map Letter
    let mkTerminal = function
        | Letter x -> Terminal x
        | Eps -> E

module internal HelpFunctions =
    open MTTypes
    open GrammarZeroTypes

    let makePair x y = (x, y)

    let Coroutine2 x y lambda =
        seq { for a in x do
              for b in y do
                  yield lambda a b }

    let fromSymbolToVar =
        Set.map (function
            | Var x -> x
            | _ -> failwith "not a variable")

    let enumerate = Seq.mapi (fun i x -> Var <| NumSymb i, x)

    let toNumed tuple = Map.findKey (fun _ -> (=) tuple)

    let inline getNums m = (Map.toSeq >> Seq.map fst >> Set.ofSeq) m // DON'T CARRY THIS FUNC

module internal MTToGrammarZero =
    open HelpFunctions
    open Primitives
    open FunctionalHelpers
    open MTTypes
    open GrammarZeroTypes
    open System.Collections.Generic
    open Prelude

    let brackets : Grammar =
        let ax = Var <| Axiom 'S'
        let prods =
            set [
                    mkProduction [ax] [Terminal '('; ax; Terminal ')'];
                    mkProduction [ax] [E];
                    mkProduction [ax] [ax;ax];
                ]
        (set[Axiom 'S'], set['('; ')'], prods, 'S')

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

        let removeEpsilon = List.filter (function E -> false | _ -> true)
        let prods = Set.map (fun (l, r) -> removeEpsilon l, removeEpsilon r) prods

        let allTerminals = List.forall (function Terminal _ -> true | _ -> false)
        let nearFinish = List.forall (function Terminal _ | Var(State _) -> true | _ -> false)
        let q = Queue<symbol list>()
        let mutable allRes : Set<symbol list> = set[]
        let mutable res = [Var <| NumSymb 19; Var <| NumSymb 19; Var <| NumSymb 19; Var <| State 0; Var <| NumSymb 8; Var <| NumSymb 0; Var <| Axiom 'C']
//        let mutable res = [Var <| State 42; Terminal '1'; Terminal '0']
        while Set.count allRes < 1 do
            Set.iter (fun (left, right) ->
                let words = exchange res left right //TODO: why set of list?
//                let words = Set.map removeEpsilon words //TODO: what if terminals E will be in the left hand side
                if not(Set.isEmpty words) then
                    let terminalWords, nonterminalWords = Set.partition allTerminals words
                    allRes <- Set.union terminalWords allRes
                    let nonterminalWords = Set.remove res nonterminalWords
                    let nonterminalWords = Set.filter (not << q.Contains) nonterminalWords
                    Set.iter q.Enqueue nonterminalWords) prods
            if q.Count <> 0 then
                res <- q.Dequeue()
                if nearFinish res then
                    q.Clear()
//                printfn "%s" <| Prelude.join " " res
//            System.Console.ReadKey() |> ignore
        allRes

    let transformation ((states, alphabet, tapeAlph, delta, initialState, finalStates) : MT) : Grammar =
        let exAlph = mkExAlphabet alphabet in
        let allTuples = Coroutine2 exAlph tapeAlph makePair in
        let AllTuplesMap : Map<symbol, notNumedSymb> = allTuples |> enumerate |> Map.ofSeq in
        let Variables : Set<var> =
            Set.union (fromSymbolToVar <| getNums AllTuplesMap) (Set.map State states)
            |> Set.add (Axiom 'A')
            |> Set.add (Axiom 'B')
            |> Set.add (Axiom 'C')
        let firstPhase =
            let axiomA = mkAxiom 'A' in
            let axiomB = mkAxiom 'B' in
            let axiomC = mkAxiom 'C' in
            set [
                mkProduction [axiomA] [tupleSymbol Eps Blank; tupleSymbol Eps Blank; tupleSymbol Eps Blank; mkState initialState; axiomB];
                mkProduction [axiomB] [axiomC];
                mkProduction [axiomC] [tupleSymbol Eps Blank; axiomC];
                mkProduction [axiomC] [E]
            ]
            |> Set.union (Set.map (fun a -> mkProduction [axiomB] [tupleSymbol (Letter a) (TLetter a); axiomB]) alphabet)
        let secondPhase =
            let deltaStepToProductions (state, symbol) (newState, newSymbol, shift) =
                match shift with
                | Right -> Seq.map (fun a -> mkProduction [mkState state; tupleSymbol a symbol] [tupleSymbol a newSymbol; mkState newState]) exAlph
                | Left  -> Coroutine2 exAlph allTuples (fun a b -> mkProduction [tupleSymbol <|| b;mkState state;tupleSymbol a symbol] [mkState newState;tupleSymbol <|| b;tupleSymbol a newSymbol])
                |> Set.ofSeq
            Map.fold (fun acc k v -> Set.union acc <| deltaStepToProductions k v) Set.empty delta
        let thirdPhase = Set.ofSeq <| Seq.concat (Coroutine2 allTuples finalStates (fun (a, C) q ->
                let q = mkState q
                let t = mkTerminal a
                let aC = tupleSymbol a C
                seq [
                    mkProduction [aC; q] [q; t; q]
                    mkProduction [q; aC] [q; t; q]
                    mkProduction [q] [E]
                ]))
        let enumerateProd = List.map (function
            | Var (NotNumedSymb symb) -> toNumed symb AllTuplesMap
            | symb -> symb)
        let numedProductions = Set.map (fun (leftProd, rightProd) -> enumerateProd leftProd, enumerateProd rightProd) <| Set.unionMany [firstPhase; secondPhase; thirdPhase]

        AllTuplesMap
        |> Map.toList
        |> List.map (fun (a, n) -> sprintf "%O -> %O" a n)
        |> join "\n"
        |> printfn "%s"

        (Variables, alphabet, numedProductions, 'A')
