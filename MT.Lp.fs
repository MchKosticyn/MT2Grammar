namespace MT
open MT.MTTypes
open MT.Primitives

module private MicroMT =
    type DeltaFuncContents = (state * trackSymbol) * (state * trackSymbol * Move)
    type OuterState =
        | YesNo of yes: OuterState * no: OuterState
        | Forward of state
        | Finish
    module OuterStateUtils =
        let rec map f = function
            | YesNo(l, r) -> YesNo(map f l, map f r)
            | Forward x -> Forward <| f x
            | Finish -> Finish

        let rec fold (f: state -> 'a -> 'a) (z: 'a) = function
            | YesNo(l, r) -> fold f (fold f z l) r
            | Forward x -> f x z
            | Finish -> z

        let max = fold max -1

    type MicroMT =
        val maxState: state
        val delta: list<DeltaFuncContents>
        val initialState: state
        val outerState: OuterState
        val finalStates: Set<state> // On which MT will 'beep'

        override this.ToString() =
            System.String.Format("INITIAL: {0}\nOUTERS: {1}\nFINALS: {2}\nDELTA:\n{3}",
                                 this.initialState, this.outerState, this.finalStates,
                                 String.concat "\n" <| List.map (fun x -> x.ToString()) this.delta)

        new (start: state, shift: int, finalStates: Set<state>, outerState: OuterState, delta: list<DeltaFuncContents>) =
            assert (start <= shift)
            let shiftButInitial = function
                | 0 -> start
                | n -> n + shift
            let finalStates = Set.map shiftButInitial finalStates
            let outerState = OuterStateUtils.map shiftButInitial outerState
            let delta : list<DeltaFuncContents> =
                List.map (fun ((p, a), (q, b, m)) -> ((shiftButInitial p, a), (shiftButInitial q, b, m))) delta

            let maxState = List.fold (fun m ((q, _), (p, _, _)) -> max q p |> max m)
                                     (if finalStates.IsEmpty then -1 else finalStates.MaximumElement)
                                     // outer states may not be included in delta
                                     delta
            {maxState=max maxState <| OuterStateUtils.max outerState; delta=delta; initialState=shift; outerState=outerState; finalStates=finalStates}

    type MicroMTCombinator = MMTC of (state -> int -> MicroMT)
    let mkMMTCombFin (finalStates: Set<state>) (outerState: OuterState) (delta: list<DeltaFuncContents>) : MicroMTCombinator =
        MMTC <| fun start shift -> new MicroMT(start, shift, finalStates, outerState, delta)
    let mkMMTCombYesNo x y = YesNo(Forward x, Forward y) |> mkMMTCombFin Set.empty
    let mkMMTComb = Forward >> mkMMTCombFin Set.empty

    let runMMTC = function MMTC f -> f

    let compose decompose nextConnector a b =
        let left = runMMTC a 0 0
        let outerState, z = decompose left.outerState
        let right = runMMTC b outerState left.maxState
        mkMMTCombFin (Set.union left.finalStates right.finalStates) (nextConnector z right.outerState) (left.delta @ right.delta)

    let (>>) = compose (function Forward outerState -> outerState, Finish) (fun _ -> id)
    let (.>>) = compose (function YesNo(Forward yes, no) -> yes, no) (fun no right -> YesNo(right, no))
    let (>>.) = compose (function YesNo(yes, Forward no) -> no, yes) (fun yes right -> YesNo(yes, right))

module private BuilderFunctions =
    open MicroMT
    let alpha : Set<letterOfAlphabet> = set ['0'; '1']
    let Sharp = ExSymbol '#'
    let Zero = TLetter '0'
    let One = TLetter '1'
    let NZero = TLetter '2'
    let NOne = TLetter '3'

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

    let cycle decompose mmtc =
        let mmt = runMMTC mmtc 0 0
        let outerState, z = decompose mmt.outerState
        let delta = substStepsOfDelta outerState 0 mmt.delta
        let finalStates = Set.map (fun st -> if st = outerState then 0 else st) mmt.finalStates
        mkMMTCombFin finalStates z delta

    let cycleYes = cycle (function YesNo(Forward yes, no) -> yes, no)
    let cycleForward = cycle (function Forward x -> x, Finish)

module private Primes =
    open MicroMT
    open BuilderFunctions

    let CHK01 : MicroMTCombinator = // [n -> $ | B[n
        [
            ((0, Zero), (1, Blank, Right)) // B[B] $
            ((0, One), (2, One, Right)) // 1[..
        ]
        @ skipBlank 2 1 Right // 1B[B] $
        @ [
            ((2, Zero), (3, Zero, Left)) // B[1]0..
            ((2, One), (3, One, Left)) // B[1]1..
            ((3, One), (4, One, Left)) // [B]11..
            ((4, Blank), (5, Blank, Left)) // [B]B11..
            ((5, Blank), (6, Blank, Left)) // [B]BB11..
            ((6, Blank), (7, InitSymb, Right)) // C[B]B1..
        ]
        @ skipBlank 7 8 Right // CB[B]1..
        @ skipBlank 8 9 Right
        |> mkMMTComb 9

    let COPY : MicroMTCombinator = // [n -> [nBn
        [
            ((0, Zero), (2, NZero, Right)) // 2[n'B
        ]
        @ skipAlpha 2 2 Right // 2n'[B]
        @ skipBlank 2 4 Right // 2n'B[m
        @ skipAlpha 4 4 Right // 2n'Bm[B]
        @ [
            ((4, Blank), (5, Zero, Left)) // M2n'Bm]0
        ]

        // same for 1
        @ [
            ((0, One), (1, NOne, Right)) // 2[n'Bx
        ]
        @ skipAlpha 1 1 Right // 3n'[B]m
        @ skipBlank 1 3 Right // 3n'B[m
        @ skipAlpha 3 3 Right // 3n'Bm[B]
        @ [
            ((3, Blank), (5, One, Left)) // M3n'Bm]1
        ]

        @ skipAlpha 5 5 Left // M?n'[B]m?
        @ skipBlank 5 5 Left // M[?]n'Bm?
        @ skipNAlpha 5 0 Right // [n'

        @ skipBlank 0 6 Left // N]Bn
        @ castNAlphaToAlpha 6 6 Left // [B]nBn
        @ skipBlank 6 7 Right
        |> mkMMTComb 7

    let DEC = // [nBx -> [nB{x-1}, x >= 2
        skipAlpha 0 0 Right
        @ skipBlank 0 1 Right
        @ skipAlpha 1 1 Right // nBx[B]
        @ skipBlank 1 2 Left  // nBx]

        @ [
            ((2, Zero), (2, One, Left))
            ((2, One), (3, Zero, Right))
        ] // nB[{x-1}B]
        @ skipAlpha 3 3 Right // nB{x-1}[B]
        @ skipBlank 3 4 Left
        @ skipAlpha 4 4 Left // n[B]{x-1}
        @ skipBlank 4 5 Left
        @ skipAlpha 5 5 Left
        @ skipBlank 5 6 Right
        |> mkMMTComb 6

    let COPY2 = // forall x . [nBx -> [nBxBn
        [
            ((0, Zero), (2, NZero, Right)) // 2[n'Bx
        ]
        @ skipAlpha 2 2 Right // 2n'[B]x
        @ skipBlank 2 4 Right // 2n'B[x
        @ skipAlpha 4 4 Right // 2n'Bx[B]
        @ skipBlank 4 6 Right // M2n'BxB[m
        @ skipAlpha 6 6 Right // M2n'BxBm[B]
        @ [
            ((6, Blank), (7, Zero, Left)) // M2n'BxBm]0
        ]

        // same for 1
        @ [
            ((0, One), (1, NOne, Right)) // 2[n'Bx
        ]
        @ skipAlpha 1 1 Right // 3n'[B]x
        @ skipBlank 1 3 Right // 3n'B[x
        @ skipAlpha 3 3 Right // 3n'Bx[B]
        @ skipBlank 3 5 Right // M3n'BxB[m
        @ skipAlpha 5 5 Right // M3n'BxBm[B]
        @ [
            ((5, Blank), (7, One, Left)) // M3n'BxBm]1
        ]

        @ skipAlpha 7 7 Left // M?n'Bx[B]m?
        @ skipBlank 7 7 Left // M[?]n'BxBm?
        @ skipNAlpha 7 0 Right // [n'Bx

        @ skipBlank 0 8 Left // N]BxBn
        @ castNAlphaToAlpha 8 8 Left // [B]nBxBn
        @ skipBlank 8 9 Right
        |> mkMMTComb 9

    let RENEW_DOLLAR = // [nBxBn{B|$} -> [nBxBnB$
        skipAlpha 0 0 Right   // n[B]xBn
        @ skipBlank 0 1 Right // nB[xBn
        @ skipAlpha 1 1 Right // nBx[B]n
        @ skipBlank 1 2 Right // nBxB[n
        @ skipAlpha 2 2 Right // nBxBn[B]
        @ skipBlank 2 3 Right // nBxBnB[B]
        @ [
            ((3, Blank), (4, EndSymb, Left))
            ((3, EndSymb), (4, EndSymb, Left))
        ]
        @ skipBlank 4 5 Left
        @ skipAlpha 5 5 Left
        @ skipBlank 5 6 Left
        @ skipAlpha 6 6 Left
        @ skipBlank 6 7 Left
        @ skipAlpha 7 7 Left
        @ skipBlank 7 8 Right
        |> mkMMTComb 8

    let CHK_MID_EQ_ONE = // [nBxBn -> $(x == 1) | nBx]Bn
        skipAlpha 0 0 Right
        @ skipBlank 0 1 Right
        @ [
            ((1, Zero), (1, Zero, Right))
            ((1, One), (2, One, Right))
        ]
        @ skipBlank 2 3 Right // $, beep
        @ skipAlpha 2 4 Right
        @ skipAlpha 4 4 Right // nBx[B]n
        @ skipBlank 4 5 Left
        |> mkMMTCombFin (set[3]) (Forward 5)

    let GOTO_MID_TO_RIGHT = // nBx]Bn -> nBxBn]
        skipAlpha 0 1 Right
        @ skipBlank 1 2 Right
        @ skipAlpha 2 2 Right
        @ skipBlank 2 3 Left
        |> mkMMTComb 3

    let RIGHT_NOT_EQ_ZERO = // xBm] -> $ | x]Bm
        [
            ((0, Zero), (0, Zero, Left))
            ((0, One), (1, One, Left))
        ]
        @ skipBlank 0 3 Left // $, == 0

        @ skipAlpha 1 1 Left
        @ skipBlank 1 2 Left
        |> mkMMTComb 2

    let RIGHT_MINUS_MID = // nBx]Bn -> `yes: nBxB{n-x}] ; no: [xB{garbage, when n%x > 0}` , x >= 2, n > 0
        let UNDIVIDABLE = 14
        skipNAlpha 0 0 Left

        // MID = 0..
        @ [((0, Zero), (1, NZero, Right))]
        @ skipNAlpha 1 1 Right
        @ skipBlank 1 2 Right
        @ skipAlpha 2 2 Right // x0'XBn[
        @ skipBlank 2 3 Left
        @ skipNAlpha 2 3 Left // x0'XBn]N
        @ [
            ((3, Zero), (4, NZero, Left)) // 2X[Bn']2
            ((3, One), (4, NOne, Left)) // 2X[Bn']3
        ]
        @ skipAlpha 4 4 Left
        @ skipBlank 4 0 Left // xX]Bn'N

        // MID = 1..
        @ [((0, One), (5, NOne, Right))]
        @ skipNAlpha 5 5 Right
        @ skipBlank 5 6 Right
        @ skipAlpha 6 6 Right // x1'XBn[
        @ skipBlank 6 7 Left
        @ skipNAlpha 6 7 Left // x1'XBn]N
        @ [
            ((7, Zero), (8, NOne, Left)) // 3X[Bn']3 // decrement
            ((7, One), (10, NZero, Left)) // 3X[Bn']2 // decrement
        ]

        @ [
            ((8, Zero), (8, One, Left))
            ((8, One), (10, Zero, Left)) // 3X[Bn']0111...113
            ((8, Blank), (UNDIVIDABLE, Blank, Right)) // 3XB[?N|n?M
        ]
        @ skipAlpha 10 10 Left
        @ skipBlank 10 0 Left

        // [B]XBN
        @ skipBlank 0 11 Right // [XBN    goto right =?= 0
        @ castNAlphaToAlpha 11 11 Right // x[B]N
        @ skipBlank 11 12 Right
        @ castNAlphaToAlpha 12 12 Right // xBn[B]
        @ skipBlank 12 13 Left

        @ skipNAlpha UNDIVIDABLE UNDIVIDABLE Left // X[Bn']N
        @ skipAlpha UNDIVIDABLE UNDIVIDABLE Left // X[B]n'N
        @ skipBlank UNDIVIDABLE 15 Right
        @ skipAlpha 15 15 Right
        @ castNAlphaToAlpha 15 15 Right
        @ skipBlank 15 16 Left
        @ skipAlpha 16 16 Left
        @ skipBlank 16 17 Left // X]Bn
        @ castNAlphaToAlpha 17 17 Left
        @ skipAlpha 17 17 Left
        @ skipBlank 17 18 Right
        |> mkMMTCombYesNo 13 18

    let CLEAN_RIGHT = // [xBgarbage -> [xB
        skipAlpha 0 0 Right
        @ skipBlank 0 1 Right
        @ [
            ((1, Zero), (1, Blank, Right))
            ((1, One), (1, Blank, Right))
        ]
        @ skipBlank 1 2 Left
        @ skipBlank 2 2 Left // x]B
        @ skipAlpha 2 3 Left // [Bx]B
        @ skipAlpha 3 3 Left
        @ skipBlank 3 4 Right
        |> mkMMTComb 4

    let RIGHT_MODULO_MID = // xBm] -> xB{m%x} -> $ | [xB
        cycleYes (
            RIGHT_NOT_EQ_ZERO
            >> RIGHT_MINUS_MID
        )
        >> CLEAN_RIGHT

    let GOTO_MID_TO_LEFT = // nB[x -> [nBx
        skipAlpha 0 0 Left
        @ skipBlank 0 1 Left
        @ skipAlpha 1 1 Left
        @ skipBlank 1 2 Right
        |> mkMMTComb 2


    let MAIN =
        CHK01
        >> COPY
        >> cycleForward (
            DEC
            >> COPY2
            >> RENEW_DOLLAR
            >> CHK_MID_EQ_ONE
            >> GOTO_MID_TO_RIGHT
            >> RIGHT_MODULO_MID
            >> GOTO_MID_TO_LEFT
        )

module internal TestMT =
    open BuilderFunctions
    open Primes
    open MicroMT

    let runMT ((_, _, _, delta, startST, finST) : MT) (word: string) =
        let track = new ResizeArray<trackSymbol>(List.map TLetter <| List.ofSeq word)
        let rec runner state index =
            let symb = track.[index]
            match Map.tryFind (state, symb) delta with
            | None -> Set.contains state finST
            | Some(state, symb', move) ->
                track.[index] <- symb'
                let index =
                    match move with
                    | Left -> index - 1
                    | Right -> index + 1
                let index =
                    match index with
                    | -1 ->
                        track.Insert(0, Blank)
                        0
                    | n when n = track.Count ->
                        track.Add(Blank)
                        index
                    | _ -> index
                runner state index

        runner startST 0

module internal BuildMT =
    open LBATypes
    open GrammarOnePrimitives
    let PrimesMT =
        let mkMT (d: deltaFunc) (alpha: Set<letterOfAlphabet>) (start: state) (fin: state Set) : MT =
            let collectStatesAndSymbols (states: state Set, track: trackSymbol Set) (stQ, symbA) (stP, symbB, _) =
                let states' = states.Add(stQ).Add(stP)
                let track' = Set.add symbA <| Set.add symbB track
                (states', track')
            let (states, track) = Map.fold collectStatesAndSymbols (Set.empty, Set.empty) d
            (states, alpha, track, d, start, fin)
        let mt = MicroMT.runMMTC Primes.MAIN 0 0
        mkMT (Map.ofList mt.delta) BuilderFunctions.alpha mt.initialState mt.finalStates
    let PrimesLBA : LBA =
        let (states, alpha, track, d, start, fin) = PrimesMT
        let track = Set.filter (function ExSymbol 'C' | ExSymbol '$' -> false | _ -> true) track
        let track = Set.map TrackSymbol track |> Set.add cent |> Set.add dollar
        let d =
            let toNormal = function
                | ExSymbol 'C' -> StartSym Cent
                | ExSymbol '$' -> EndSym Dollar
                | t -> TrackSymbol t
            Map.toList d |> List.map (fun ((p, a), (q, b, m)) -> (p, toNormal a), (q, toNormal b, m)) |> Map.ofList
        (states, alpha, track, d, start, fin)
