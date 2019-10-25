import cfr

def dice := list.to_buffer [1,2,3,4,5,6]
def claims := list.to_buffer [(1,2), (1,3), (1,4), (1,5), (1,6), (1,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,1)]
def AllowedClaim := {i // ∃ v, claims.read i = v}
instance : has_lt AllowedClaim := ⟨ fun a b, a.val < b.val ⟩ 
instance AllowedClaim_decidable_rel : decidable_rel ((<) : AllowedClaim → AllowedClaim → Prop) := infer_instance

inductive Action
| Claim (claim : AllowedClaim) : Action
| Dudo : Action

def Action.show : Action → string
| (Action.Claim ⟨ i, _⟩ ) := "Claim " ++ has_repr.repr (claims.read i)
| Action.Dudo := "Dudo"

instance : has_repr Action := ⟨ Action.show ⟩

def actions.begin := claims.attach_index.iterate buffer.nil (fun i x s, s.push_back $ Action.Claim x)
def actions.later := actions.begin.push_back Action.Dudo

def Die := {die // die ∈ dice}
instance : has_lt Die := ⟨ fun a b, a.val < b.val ⟩
instance Die_decidable_rel : decidable_rel ((<) : Die → Die → Prop) := infer_instance

@[derive has_lt] def History := Die × list AllowedClaim
instance History_decidable_rel : decidable_rel ((<) : History → History → Prop) := infer_instance

def ha : HistoryToActions History Action
    | (_, []) := ⟨ actions.begin.1, actions.begin.read ⟩
    | (_, x :: xs) := 
        -- TODO: The way buffer.drop behaves on out of bounds is wonky. Replace it.
        let v := actions.later.drop (x.1 + 1) in ⟨ v.1, v.read ⟩

structure Particle (α : Type*) := mk ::
    (state : α)
    (probability : ℚ)
    (infosets : Infosets ha)
    (is_updateable : bool)

namespace game
def state := state (Infosets ha)
def read_dice (i : fin dice.1) : Die := ⟨ dice.read i, ⟨ i, rfl ⟩ ⟩

def chance (one : Particle unit) (next : Particle Die → state rat) : state rat := 
    chance_uniform ha ⟨ dice.1, read_dice ⟩ one.probability 
        (fun dice prob, next {state:=dice, probability:=prob*one.probability, ..one})

def response (one two : Particle Die) (h : list AllowedClaim)
        (next : Action → Particle Die → state rat) 
        : state rat :=
    response ha one.is_updateable one.probability two.probability ⟨ one.state, h ⟩
        (fun action prob, next action {probability:=prob, ..one}) 

def terminal := terminal ha

end game

