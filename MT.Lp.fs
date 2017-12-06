namespace MT
open MT.MTTypes
open MT.Primitives

module private MicroMT =
    type DeltaFuncContents = (state * trackSymbol) * (state * trackSymbol * Move)
    type OuterState =
        | YesNo of yes: OuterState * no: OuterState
        | Forward of state
        | Finish
    module OuterState =
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
            let outerState = OuterState.map shiftButInitial outerState
            let delta : list<DeltaFuncContents> =
                List.map (fun ((p, a), (q, b, m)) -> ((shiftButInitial p, a), (shiftButInitial q, b, m))) delta

            let maxState = List.fold (fun m ((q, _), (p, _, _)) -> max q p |> max m)
                                     (if finalStates.IsEmpty then -1 else finalStates.MaximumElement)
                                     // outer states may not be included in delta
                                     delta
            {maxState=max maxState <| OuterState.max outerState; delta=delta; initialState=shift; outerState=outerState; finalStates=finalStates}

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
    // BAD: 1
    let CHK01 : MicroMTCombinator = // [n -> $ | [B]n
        [
            ((0, Zero), (1, Blank, Right)) // B[B] $
            ((0, One), (2, One, Right)) // 1[..
        ]
        @ skipBlank 2 1 Right // 1B[B] $
        @ [
            ((2, One), (3, One, Left)) // [B]1..
            ((3, Blank), (4, Blank, Left)) // [B]B1..
            ((4, Blank), (5, InitSymb, Right)) // C[B]1..
        ]
        @ skipBlank 5 5 Right
        |> mkMMTComb [5] // out is 5

    let COPY : MicroMTCombinator = // [n -> [nBn
        skipAlpha 0 1 Left // [B]n
        @ [((1, Blank), (2, Sharp, Right))] // #[n
        @ castNAlphaToAlpha 2 2 Right // #x[n, x: NA, n: A
        @ [
            ((2, TLetter '0'), (3, ExSymbol '#', Left))   // [#]#n'
            ((3, ExSymbol '#'), (5, TLetter '0', Right))  // 0[#]n'
            ((5, ExSymbol '#'), (7, ExSymbol '#', Right)) // 0#[n'
            ((7, ExSymbol 'B'), (9, TLetter '2', Left))   // 0#n'N[B] -> 0#n'N]2
            ((2, TLetter '1'), (4, ExSymbol '#', Left))   /// same
            ((4, ExSymbol '#'), (6, TLetter '1', Right))  /// for
            ((6, ExSymbol '#'), (8, ExSymbol '#', Right)) /// the
            ((8, ExSymbol 'B'), (9, TLetter '3', Left))   /// ones
        ]
        @ skipAll 7 7 Right // 0#[n' -> 0#n'[B]
        @ skipAll 8 8 Right
        @ skipAll 9 9 Left // 0#n'N]2 -> 0[#]n'N2  (merge forks)
        @ [((9, Sharp), (2, Sharp, Right))] // 0#[n'N2
        @ skipBlank 2 10 Left // n#n[B] -> n#n]
        @ skipAlpha 10 10 Left // n[B]n
        @ [((10, Sharp), (11, Blank, Left))] // n]Bn
        @ skipAlpha 11 11 Left // [B]nBn
        @ skipBlank 11 12 Right // [nBn
        |> mkMMTComb [12]

    let GOTO_RIGHT = // [n'BxBa -> n'BxBa[B]
        skipAlpha 0 0 Right // [n'BxBa -> n'[B]xBa
        @ skipBlank 0 1 Right // n'B[xBa
        @ skipAlpha 1 1 Right // n'Bx[B]a
        @ skipBlank 1 2 Right // n'BxB[a
        @ skipAlpha 2 2 Right // n'BxBa[B]
        |> mkMMTComb [2]

    let COPY2 : MicroMTCombinator = // forall x . [nBx -> [nBxBn
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
            let cast x =
                if x = Zero then NZero
                else if x = One then NOne
                else x
            (symb, cast symb, Right, GOTO_RIGHT >> mkMMTComb [1] [((0, Blank), (1, symb, Left))]) // [snBxBa -> SnBxBa]s
        cycle (
            fork [
                copy1symb Zero
                copy1symb One
            ]
            >> GOTO_LEFT)
        |> addToInitial Blank Blank Left // N]BxBn
        >> CLEAN

    let INSERT_Sharp_End = // nBxBn[B] -> nBx]Bn#$
        [
            ((0, Blank), (1, Sharp, Right)) // nBxBn#[B]
            ((1, Blank), (2, EndSymb, Left)) // nBxBn[#]$
            ((1, EndSymb), (2, EndSymb, Left)) // already have $
            ((2, Sharp), (2, Sharp, Left))

        ]
        @ skipAlpha 2 2 Left // nBx[B]n#
        @ skipBlank 2 3 Left // nBx]Bn#
        |> mkMMTComb [3]

    let GOTO_Sharp = // [NB]x# -> NBx]#
        skipNAlpha 0 0 Right
        @ skipBlank 0 1 Right
        @ skipAlpha 1 1 Right
        @ [((1, Sharp), (2, Sharp, Left))]
        |> mkMMTComb [2]

    let UNSAFE_DEC_MID = // n]B -> {n-1}]B, n >= 1 for proper work
        [
            ((0, Zero), (0, One, Left))
            ((0, One), (1, Zero, Right))
        ]
        @ skipAlpha 1 1 Right
        @ skipBlank 1 2 Left
        |> mkMMTComb [2]

    let RIGHT_MINUS_MID = // x]Bn# -> $ | if n <= x then xX'B[{1^t}#g (lower st) else xB{n-x}[B] (higher st)
        let SHIFT_Sharp = // n[NBxs]#y -> nN]Bx#sy
            let SWAP_Sharp = // nNBxs]#y -> nN]Bx#sy
                [
                    ((0, Zero), (1, Sharp, Right))
                    ((1, Sharp), (3, Zero, Left))
                    ((0, One), (2, Sharp, Right))
                    ((2, Sharp), (3, One, Left))
                    ((3, Sharp), (4, Sharp, Left))
                ]
                @ skipAlpha 4 4 Left
                @ skipBlank 4 5 Left
                |> mkMMTComb [5]

            mkMMTComb [0] <| skipAlpha 0 0 Left // n[NB]xs#y
            >> GOTO_Sharp // nNBxs]#y
            >> SWAP_Sharp

        let DEC_L = // xX'Bt]# -> if n <= x then xX'B[{1^t}#g else xX'B[{t-1}]#
            [
                ((0, Blank), (1, Blank, Right)) // xX'[B]{1^t}#g -> xX'B[{1^t}#g //// n <= x, so RETURN
                ((0, Zero), (0, One, Left)) // \ DEC
                ((0, One), (2, Zero, Left)) // / DEC
            ]
            |> mkMMTComb [1; 2]

        let CAST_AND_CLEAN = // B[XB{0*}#t -> BxB{0+}t[B]
            castNAlphaToAlpha 0 0 Right
            @ skipBlank 0 1 Right
            @ [
                ((1, Zero), (1, Zero, Right))
                ((1, Sharp), (2, Zero, Right))
            ]
            @ skipAlpha 2 2 Right
            |> mkMMTComb [2]

        cycle (
            mkMMTComb [0] <| skipNAlpha 0 0 Left // x[X]Bt# -> x]XBt#
            >> fork [
                (Zero, NZero, Right, mkMMTComb [1] []) // x[0]X'Bt# -> x2[X'Bt#
                (One, NOne, Right, GOTO_Sharp >> DEC_L) // x[1]X'Bt# -> x3[X'Bt# -> x3X'[B{t-1}]#
            ]
            >> SHIFT_Sharp) // the only escape from cycle is `1` state of DEC_L
        |> addToInitial Blank Blank Right // B[XB{0*}#t // results in 2 outer states! //// n -= x SUCCEDED
        >> CAST_AND_CLEAN

    let RIGHT_MODULO_MID = // nBx]Bn# -> nBx'X'B[{1^t}#g
        cycle (                             //// while right > mid
               RIGHT_MINUS_MID              ////     right -= mid
            >> INSERT_Sharp_End)

    let CHK_RIGHT_ROUGHLY_ZERO_EQUAL = // nBx'X'B[{1^t}#g -> $ (g == 0) | [nBx
        let SHIFT_LEFT = // [#]gB$ -> g]BB$
            [
                ((0, Sharp), (1, Sharp, Right)) // #[gB$
                ((1, Zero), (2, Sharp, Left))   // #]#g'B$
                ((2, Sharp), (0, Zero, Right))  // 0[#]g'B$
                ((1, One), (3, Sharp, Left))    // #]#g'B$
                ((3, Sharp), (0, One, Right))   // 1[#]g'B$
                ((1, Blank), (4, Blank, Left))  // g[#]B$
                ((4, Sharp), (5, Blank, Left)) // g]BB$
            ]
            |> mkMMTComb [5]

        let CAST_MID = // nBx[{B+}]$ -> [nBxy
            skipBlank 0 0 Left // nBxY]
            @ castNAlphaToAlpha 0 0 Left // nBx]y
            @ skipAlpha 0 1 Left
            @ skipAlpha 1 1 Left // n[B]xy
            @ skipBlank 1 2 Left
            @ skipAlpha 2 2 Left
            @ skipBlank 2 3 Right
            |> mkMMTComb [3]

        mkMMTComb [0] [((0, One), (0, Blank, Right))] // nBx{B^t+1}[#]g
        >> SHIFT_LEFT // nBx{B^t+1}g]BB$
        >> mkMMTComb [1] [
            ((0, Zero), (0, Blank, Left)) // nBx{B^t+1}k]{BB+}$, where k = g'1 or nothing
            ((0, Blank), (2, Blank, Left)) // 2 is DEAD END
            ((0, One), (1, Blank, Left)) // nBx{B^t+1}g']{B+}$
            ((1, Zero), (1, Blank, Left))
            ((1, One), (1, Blank, Left)) // nBx[{B+}]$
        ]
        >> CAST_MID

    let CHK_MID_ONE_EQUAL = // nBx]B -> $ (x == 1) | n]Bx#
        [
            ((0, One), (1, One, Left)) // found 1
            ((0, Zero), (2, Zero, Right)) // nBx[B]
            ((1, Zero), (1, Zero, Left)) // keep checking 1 == 01 == 001 == ...
            ((1, Blank), (3, Blank, Right)) // (x == 1) GOOD END
            ((1, One), (2, One, Right)) // nB[x]B
        ]
        @ skipAlpha 2 2 Right // nBx[B]
        @ [((2, Blank), (4, Sharp, Left))] // nBx]#
        @ skipAlpha 4 4 Left
        @ skipBlank 4 5 Left
        |> mkMMTCombFin (set[3]) (set[5]) // FINAL is 3, Outer is 5

    let MAIN =
        CHK01                                   //// if n = 0 or n = 1 then return false
        >> COPY                                 //// mid := n // mid >= 2
        >> cycle (
               COPY2                            //// right := n
            >> GOTO_RIGHT
            >> INSERT_Sharp_End
            >> UNSAFE_DEC_MID                   //// mid-- // mid >= 1
            >> CHK_MID_ONE_EQUAL // beep!       //// if mid = 1 then return true
            >> RIGHT_MODULO_MID                 //// right %= mid
            >> CHK_RIGHT_ROUGHLY_ZERO_EQUAL     //// IF right = 0 THEN return false ELSE right := <blanks>
        )

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
