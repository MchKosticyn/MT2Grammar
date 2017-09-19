// types : MT
type letterOfAlphabet = char
type exSymbol = char
type state = int
type trackSymbol = TLetter of letterOfAlphabet | ExSymbol of exSymbol
type shift = Right | Left
type deltaFunc = Map<state * trackSymbol, state * trackSymbol * shift>
type MT = state Set * letterOfAlphabet Set * trackSymbol Set * deltaFunc * state * state Set
