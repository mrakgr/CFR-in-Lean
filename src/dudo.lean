import cfr

def list_dice := [1,2,3,4,5,6]
def list_claim := [(1,2), (1,3), (1,4), (1,5), (1,6), (1,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,1)]

inductive Action
| Claim (claim : {n // n ∈ list_claim}) : Action
| Dudo : Action

def actions.begin := list_claim.attach.map Action.Claim
def actions.later := actions.begin ++ [Action.Dudo]

def Action.show : Action → string
| (Action.Claim claim) := "Claim " ++ has_repr.repr claim.val
| Action.Dudo := "Dudo"

instance : has_repr Action := ⟨ Action.show ⟩

structure Particle {ℍ 𝔸 : Type*} [has_lt ℍ] (ha : HistoryToActions ℍ 𝔸) := mk ::
    (state : {die // die ∈ list_dice})
    (probability : ℚ)
    (infosets : Infosets ha)
    (is_updateable : bool)

