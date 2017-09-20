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
            assert (Set.isSuperset states <| Set.union finalStates outerStates)
            {states=states; delta=delta; initialState=shift; outerStates=outerStates; finalStates=finalStates}
        new (shift: int, outerStates: Set<state>, delta: list<DeltaFuncContents>) =
            new MicroMT(shift, set[], outerStates, delta)
        new (shift: int, outerState: state, delta: list<DeltaFuncContents>) =
            new MicroMT(shift, set[], Set.singleton outerState, delta)

    type MicroMTCombinator = MMTC of (int -> MicroMT)
    let mkMMTComb (outerStates: list<state>) (delta: list<DeltaFuncContents>) : MicroMTCombinator =
        MMTC <| fun shift -> new MicroMT(shift, Set.ofList outerStates, delta)
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
    let genAlpha (q: state) (p: state) (m: Move) : list<DeltaFuncContents> =
        [((q, Zero), (p, Zero, m)); ((q, One), (p, One, m))]
    let genNAlpha (q: state) (p: state) (m: Move) : list<DeltaFuncContents> =
        [((q, NZero), (p, NZero, m)); ((q, NOne), (p, NOne, m))]
    let genAll (q: state) (p: state) (m: Move) : list<DeltaFuncContents> =
        genAlpha q p m @ genNAlpha q p m
    let genNAlphaToAlpha (q: state) (p: state) (m: Move) : list<DeltaFuncContents> =
        [((q, NZero), (p, Zero, m)); ((q, NOne), (p, One, m))]
    let fork (states: list<DeltaFuncContents>) : list<DeltaFuncContents> =
        let start : int = fold1 (fun ((q, _), (p, _, _)) -> min q p) (fun m ((q, _), (p, _, _)) -> min q p |> min m) states
        let fin   : int = List.fold (fun m ((q, _), (p, _, _)) -> max q p |> max m) -1 states
        let shiftRest q = if q = start || q = fin then q else q + 1
        let flip = List.map (fun ((q, a), (p, b, m)) -> ((shiftRest q, flipT a), (shiftRest p, flipT b, m)))
        states @ flip states


    // BAD: 1
    let CHK01 : MicroMTCombinator = // if input in {0, 1} then false else GOTO 3
            [
                ((0, Zero), (1, Blank, Right)) // == 0
                ((0, One), (2, One, Right))
                ((2, Blank), (1, Blank, Right)) // == 1
            ]
            @ genAlpha 2 3 Left // go back
            |> mkMMTComb [3] // out is 3

    let COPY : MicroMTCombinator = // [n -> [nBn
        genAlpha 0 1 Left // [B]n
        @ [((1, Blank), (2, Sharp, Right))] // #[n
        @ genNAlphaToAlpha 2 2 Right // #x[n, x: NA, n: A
        @ fork [
            ((2, Zero), (3, Sharp, Left)) // [#]#n'
            ((3, Sharp), (5, Zero, Right)) // 0[#]n'
            ((5, Sharp), (7, Sharp, Right)) // 0#[n'
            ((7, Blank), (9, NZero, Left)) // 0#n'N[B] -> 0#n'N]2
        ]
        @ genAll 7 7 Right // 0#[n' -> 0#n'[B]
        @ genAll 9 9 Left // 0#n'N]2 -> 0[#]n'N2  (merge forks)
        @ [
            ((9, Sharp), (2, Sharp, Right)) // 0#[n'N2
            ((2, Blank), (10, Blank, Left)) // n#n[B] -> n#n]
        ]
        @ genAlpha 10 10 Left // n[B]n
        @ [((10, Sharp), (11, Blank, Left))] // n]Bn
        @ genAlpha 11 11 Left // [B]nBn
        @ [((11, Blank), (12, Blank, Right))] // [nBn
        |> mkMMTComb [12]


module Test =
    open Primes
    [<EntryPoint>]
    let main _ =

        0
