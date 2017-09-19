module MT.Lp
open MT.ToGrammar

let mkMT (d: deltaFunc) (alpha: letterOfAlphabet Set) (start: state) (fin: state Set) : MT =
    let collectStatesAndSymbols (states: state Set, track: trackSymbol Set) (stQ, symbA) (stP, symbB, _) =
        let states' = states.Add(stQ).Add(stP)
        let track' =
            let add = function TLetter _ as s -> Set.add s | _ -> id
            add symbA track |> add symbB
        (states', track')
    let (states, track) = Map.fold collectStatesAndSymbols (Set.empty, Set.empty) d
    (states, alpha, track, d, start, fin)
