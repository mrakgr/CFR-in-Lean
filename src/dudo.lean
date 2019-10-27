import cfr

example (a b : rat) : (¬ a < b) ∧ (¬ b < a) → a = b := by exact eq_of_incomp

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

def actions.begin := claims.attach_index
def actions.later := (actions.begin.iterate buffer.nil (fun i x s, s.push_back $ Action.Claim x)).push_back Action.Dudo

def Die := {die // die ∈ dice}
instance : has_lt Die := ⟨ fun a b, a.val < b.val ⟩
instance Die_decidable_rel : decidable_rel ((<) : Die → Die → Prop) := infer_instance

@[derive has_lt] def History := Die × list AllowedClaim
instance History_decidable_rel : decidable_rel ((<) : History → History → Prop) := infer_instance

def ℍ𝔸 : History → Type*
    | (die, []) := AllowedClaim
    | (die, _) := Action

def ha : HistoryToActions History ℍ𝔸
    | (_, []) := ⟨ actions.begin.1, actions.begin.read ⟩
    | (_, x :: xs) := 
        -- TODO: The way buffer.drop behaves on out of bounds is wonky. Replace it.
        let v := actions.later.drop (x.1 + 1) in ⟨ v.1, v.read ⟩

structure Particle (α : Type*) := mk ::
    (state : α)
    (probability : ℚ)
    (is_updateable : bool)

namespace game
def state := state (Infosets ha)
def read_dice (i : fin dice.1) : Die := ⟨ dice.read i, ⟨ i, rfl ⟩ ⟩

def chance (one : Particle unit) (next : Particle Die → state rat) : state rat := 
    chance_uniform ha ⟨ dice.1, read_dice ⟩ one.probability 
        (fun dice prob, next {state:=dice, probability:=prob*one.probability, ..one})

def response (one two : Particle Die) (h : list AllowedClaim)
        (next : ℍ𝔸 ⟨ one.state, h ⟩ → Particle Die → state rat) 
        : state rat :=
    response ha one.is_updateable one.probability two.probability ⟨ one.state, h ⟩
        (fun action prob, next action {probability:=prob, ..one}) 

def terminal := terminal ha

meta def dudo.main : Particle Die → Particle Die → list AllowedClaim → state rat
    | one two [] := response one two [] (fun action one, dudo.main two one [action])
    | one two h@(⟨i, _⟩ :: _) :=
        response one two h $ fun action one, 
            match action with
            | Action.Dudo := 
                let (number, rank) := claims.read i in
                let check_guess (s x : nat) := if x = 1 ∨ x = rank then s+1 else s in
                let dice_guessed := check_guess (check_guess 0 one.state.val) two.state.val in
                terminal $ if dice_guessed < number then 1.0 else -1.0                    
            | Action.Claim claim := dudo.main two one (claim :: h)
            end

meta def dudo.initial (one : Particle unit) (two : Particle unit) : state rat :=
    chance one $ fun one, 
        chance two $ fun two, 
            dudo.main one two []

meta def train (num_iterations : nat): rat × Infosets ha :=
    let particle : Particle unit := {state:=(), probability:=1, is_updateable:=ff} in
    let particle_tt : Particle unit := {is_updateable:=tt, ..particle} in
    @nat.foldl.fin (fun i, rat × Infosets ha) 
        num_iterations (0, buffer.nil) 
        (fun i ⟨ util, infosets ⟩,
            let (util, infosets) := (dudo.initial {is_updateable:=tt, ..particle} particle).run infosets in
            let (util', infosets) := (dudo.initial particle {is_updateable:=tt, ..particle}).run infosets in
            ((util + util') / 2, infosets)
            )

end game