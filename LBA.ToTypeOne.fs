namespace MT
open MTTypes

module internal LBATypes =
    type axiom = char
    type notNumedSymb = State of state | TapeAlph of trackSymbol
    type tuple = list<notNumedSymb>
    type var = NumSymb of int | Axiom of axiom
    type terminal = letterOfAlphabet
    type symbol = Var of var | Terminal of terminal
    type production = symbol list * symbol list
    type Grammar = var Set * letterOfAlphabet Set * production Set * axiom

//module GrammarOnePrimitives =


module internal LBAToGrammarOne =
    open Primitives
    open LBATypes

    let transformationT1 ((states, alphabet, tapeAlph, delta, initialState, finalStates) : MT) : Grammar =
        let AllTuples =
        let prod = set [
                mkProduction [mkAxiom 'A'] [Var <| ]

            ]
        prod