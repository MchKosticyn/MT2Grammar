module MT.ToGrammar
// types : MT
type letterOfAlphabet = char
type exSymbol = char
type state = int
type trackSymbol = TLetter of letterOfAlphabet | ExSymbol of exSymbol
type Move = Right | Left
type deltaFunc = Map<state * trackSymbol, state * trackSymbol * Move>
type MT = state Set * letterOfAlphabet Set * trackSymbol Set * deltaFunc * state * state Set
