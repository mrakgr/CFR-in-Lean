import data.rat
import data.list data.vector

inductive Game (players : list nat) 
| Terminal (player : {i // i ∈ players}) (reward : rat) : Game
| Response (player : {i // i ∈ players}) (subnodes : list Game) : Game 
| Chance (player : {i // i ∈ players}) (subnodes : list Game) : Game

inductive InfosetedGame (players : list string) (infoset_count : nat) (infoset_sizes : fin infoset_count → ℕ)
| Terminal (player : {i // i ∈ players}) (reward : rat) : InfosetedGame
| Response
    (player : {i // i ∈ players})
    (infoset_id : fin infoset_count)
    (subnodes : fin (infoset_sizes infoset_id) → InfosetedGame)
    : InfosetedGame
| Chance (player : {i // i ∈ players})
    {n} (subnodes : fin n → InfosetedGame) : InfosetedGame

