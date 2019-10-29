import data.rat
import data.list data.vector

inductive InfosetedGame {infoset_count : nat} (infoset_sizes : fin infoset_count → ℕ)
| Terminal (reward : rat) : InfosetedGame
| Response (infoset_id : fin infoset_count) (subnodes : fin (infoset_sizes infoset_id) → InfosetedGame) : InfosetedGame



