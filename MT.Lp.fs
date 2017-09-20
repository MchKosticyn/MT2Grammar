namespace MT.Lp
open MT.ToGrammar

module Utils =
    let __notImplemented__() = failwith "Not Implemented"

    let fold1 (once: 'a -> 'b) (f: 'b -> 'a -> 'b) = function x::xs -> List.fold f (once x) xs

    let mkMT (d: deltaFunc) (alpha: Set<letterOfAlphabet>) (start: state) (fin: state Set) : MT =
        let collectStatesAndSymbols (states: state Set, track: trackSymbol Set) (stQ, symbA) (stP, symbB, _) =
            let states' = states.Add(stQ).Add(stP)
            let track' =
                let add = function TLetter _ as s -> Set.add s | _ -> id
                add symbA track |> add symbB
            (states', track')
        let (states, track) = Map.fold collectStatesAndSymbols (Set.empty, Set.empty) d
        (states, alpha, track, d, start, fin)

module Primes =
    open Utils

    type DeltaFuncContents = (state * trackSymbol) * (state * trackSymbol * Move)
    type MicroMT =
        val states: Set<state>
        val delta: list<DeltaFuncContents>
        val initialState: state
        val outerStates: Set<state> // connectors
        val finalStates: Set<state> // On which MT will 'beep'

        new () = {states=set[]; delta=[]; initialState=0; outerStates=set[]; finalStates=set[]}
        new (shift: int, finalStates: Set<state>, outerStates: Set<state>, delta: list<DeltaFuncContents>) =
            let shiftBy = Set.map ((+) shift)
            let finalStates = shiftBy finalStates
            let outerStates = shiftBy outerStates
            let delta : list<DeltaFuncContents> =
                List.map (fun ((p, a), (q, b, m)) -> ((p + shift, a), (q + shift, b, m))) delta
            let states = List.fold (fun stts ((p, _), (q, _, _)) -> Set.add p stts |> Set.add q) (set[]) delta
            assert (Set.isSuperset states <| Set.union finalStates outerStates) // states are ALL states
            assert (List.isEmpty <| List.filter (fun ((p, _), (q, _, _)) -> p = q && Set.contains p outerStates) delta) // cycles in outer
            assert (Set.isEmpty <| Set.intersect finalStates outerStates) // final states can't be outer
            {states=states; delta=delta; initialState=shift; outerStates=outerStates; finalStates=finalStates}
        new (shift: int, outerStates: Set<state>, delta: list<DeltaFuncContents>) =
            new MicroMT(shift, set[], outerStates, delta)
        new (shift: int, outerState: state, delta: list<DeltaFuncContents>) =
            new MicroMT(shift, set[], Set.singleton outerState, delta)

    type MicroMTCombinator = MMTC of (int -> MicroMT)
    let mkMMTCombFin (finalStates: Set<state>) (outerStates: Set<state>) (delta: list<DeltaFuncContents>) : MicroMTCombinator =
        MMTC <| fun shift -> new MicroMT(shift, finalStates, outerStates, delta)
    let mkMMTComb outer = mkMMTCombFin Set.empty (Set.ofList outer)

    let mkSingleMMTC a b m = mkMMTComb [1] [((0, a), (1, b, m))]

    let runMMTC (x: MicroMTCombinator) shift =
        match x with MMTC f -> f shift

    let (>>) (a: MicroMTCombinator) (b: MicroMTCombinator) : MicroMTCombinator =
        let runner shift =
            let left = runMMTC a shift
            if left.outerStates.Count = 1
            then
                let right = runMMTC b left.outerStates.MinimumElement
                new MicroMT(shift, Set.union left.finalStates right.finalStates, right.outerStates, left.delta @ right.delta)
            else __notImplemented__()
        MMTC runner


    let alpha : Set<letterOfAlphabet> = set ['0'; '1']
    let Blank = ExSymbol 'B'
    let Sharp = ExSymbol '#'
    let Zero = TLetter '0'
    let One = TLetter '1'
    let NZero = TLetter '2'
    let NOne = TLetter '3'
    let flipT x =
        if x = Zero then One
        else if x = NZero then NOne
        else x
    let cast x =
        if x = Zero then NZero
        else if x = One then NOne
        else x
    let skipBlank q p m : list<DeltaFuncContents> =
        [((q, Blank), (p, Blank, m))]
    let skipAlpha (q: state) (p: state) (m: Move) : list<DeltaFuncContents> =
        [((q, Zero), (p, Zero, m)); ((q, One), (p, One, m))]
    let skipNAlpha (q: state) (p: state) (m: Move) : list<DeltaFuncContents> =
        [((q, NZero), (p, NZero, m)); ((q, NOne), (p, NOne, m))]
    let skipAll (q: state) (p: state) (m: Move) : list<DeltaFuncContents> =
        skipAlpha q p m @ skipNAlpha q p m
    let castNAlphaToAlpha (q: state) (p: state) (m: Move) : list<DeltaFuncContents> =
        [((q, NZero), (p, Zero, m)); ((q, NOne), (p, One, m))]

    let substStepsOfDelta fromS toS =
        let substState q = if q = fromS then toS else q
        List.map (fun ((q, a), (p, b, m)) -> ((substState q, a), (substState p, b, m)))

    let fork (cases: list<trackSymbol * trackSymbol * Move * MicroMTCombinator>) : MicroMTCombinator =
        let rec loop shift states finalStates (mergeDeltas: state -> list<DeltaFuncContents>)=
            function
            | [] -> mkMMTCombFin finalStates (set[shift]) (mergeDeltas shift)
            | (fromL, toL, mv, mts)::mtss ->
                let mt = runMMTC mts shift
                let outerState = mt.outerStates.MaximumElement
                loop (mt.states.MaximumElement + 1)
                     (Set.union states <| Set.remove outerState mt.states)
                     (Set.union finalStates mt.finalStates)
                     (fun lastState ->
                        ((0, fromL), (shift, toL, mv))
                        :: substStep outerState lastState mt.delta
                        @ mergeDeltas lastState)
                     mtss
        loop 1 Set.empty Set.empty (fun _ -> []) cases

    let cycle (mt: MicroMTCombinator) : MicroMTCombinator =
        __notImplemented__()

    let addToInitial (fromS: trackSymbol) (toS: trackSymbol) (m: Move) (mtc: MicroMTCombinator) : MicroMTCombinator =
        let runner shift =
            let mt = runMMTC mtc 0
            let freshState = mt.states.MaximumElement + 1
            let newStep = ((0, fromS), (freshState, toS, m))
            new MicroMT(shift, mt.finalStates, Set.add freshState mt.outerStates, newStep :: mt.delta)
        MMTC runner

    let dup (states: list<DeltaFuncContents>) : list<DeltaFuncContents> =
        let start : int = fold1 (fun ((q, _), (p, _, _)) -> min q p) (fun m ((q, _), (p, _, _)) -> min q p |> min m) states
        let fin   : int = List.fold (fun m ((q, _), (p, _, _)) -> max q p |> max m) -1 states
        let shiftRest q = if q = start || q = fin then q else q + 1
        let flip = List.map (fun ((q, a), (p, b, m)) -> ((shiftRest q, flipT a), (shiftRest p, flipT b, m)))
        states @ flip states


    // BAD: 1
    let CHK01 : MicroMTCombinator = // [n -> $ | [n
        [
            ((0, Zero), (1, Blank, Right)) // B[B] $
            ((0, One), (2, One, Right)) // 1[..
        ]
        @ skipBlank 2 1 Right // 1B[B] $
        @ [((2, One), (3, One, Left))] // [1]..
        |> mkMMTComb [3] // out is 3

    let COPY : MicroMTCombinator = // [n -> [nBn
        skipAlpha 0 1 Left // [B]n
        @ [((1, Blank), (2, Sharp, Right))] // #[n
        @ castNAlphaToAlpha 2 2 Right // #x[n, x: NA, n: A
        @ dup ([
                ((2, Zero), (3, Sharp, Left)) // [#]#n'
                ((3, Sharp), (5, Zero, Right)) // 0[#]n'
                ((5, Sharp), (7, Sharp, Right)) // 0#[n'
                ((7, Blank), (9, NZero, Left)) // 0#n'N[B] -> 0#n'N]2
            ]
            @ skipAll 7 7 Right) // 0#[n' -> 0#n'[B]
        @ skipAll 9 9 Left // 0#n'N]2 -> 0[#]n'N2  (merge forks)
        @ [((9, Sharp), (2, Sharp, Right))] // 0#[n'N2
        @ skipBlank 2 10 Left // n#n[B] -> n#n]
        @ skipAlpha 10 10 Left // n[B]n
        @ [((10, Sharp), (11, Blank, Left))] // n]Bn
        @ skipAlpha 11 11 Left // [B]nBn
        @ skipBlank 11 12 Right // [nBn
        |> mkMMTComb [12]

    let COPY2 : MicroMTCombinator = // forall x . [nBx -> [nBxBn
        let GOTO_RIGHT = // [n'BxBa -> n'BxBa[B]
            skipAlpha 0 0 Right // [n'BxBa -> n'[B]xBa
            @ skipBlank 0 1 Right // n'B[xBa
            @ skipAlpha 1 1 Right // n'Bx[B]a
            @ skipBlank 1 2 Right // n'BxB[a
            @ skipAlpha 2 2 Right // n'BxBa[B]
            |> mkMMTComb [2]
        let GOTO_LEFT = // Nn'BxBa] -> N[n'BxBa
            skipAlpha 0 0 Left // Nn'Bx[B]a
            @ skipBlank 0 1 Left // Nn'Bx]Ba
            @ skipAlpha 1 1 Left // Nn'[B]xBa
            @ skipBlank 1 2 Left // Nn']BxBa
            @ skipAlpha 2 2 Left // N]n'BxBa
            @ skipNAlpha 2 3 Right // N[n'BxBa
            |> mkMMTComb [3]
        let CLEAN = // N]BxBn -> [nBxBn
            castNAlphaToAlpha 0 0 Left // [B]nBxBn
            @ skipBlank 0 1 Right
            |> mkMMTComb [1]
        let copy1symb symb =
            (symb, cast symb, Right, GOTO_RIGHT >> mkSingleMMTC Blank symb Left) // [snBxBa -> SnBxBa]s
        cycle (
            fork [
                copy1symb Zero
                copy1symb One
            ]
            >> GOTO_LEFT)
        |> addToInitial Blank Blank Left // N]BxBn
        >> CLEAN

module Test =
    open Primes
    [<EntryPoint>]
    let main _ =

        0
