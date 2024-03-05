type loc = Lexing.position * Lexing.position
type 'v locatable = { loc : loc option; value : 'v }

let dummy_pos : loc = (Lexing.dummy_pos, Lexing.dummy_pos)
let mk_locatable loc value = { loc; value }
let mk_dummy_loc value = { value; loc = None }
