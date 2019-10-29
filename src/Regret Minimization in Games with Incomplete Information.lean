import data.rat

constant Infoset : Type
constant Policy : Type

def maximize {α : Type} : α × list α → (α → ℚ) → ℚ | (x,xs) f := xs.foldl (fun s a, max s (f a)) (f x)
def list.fsum {α : Type} : (α → ℚ) → list α → ℚ | f l := l.foldl (fun s a, s + f a) 0
-- Compared to the paper, here I am moving the indexing so it obeys the C notation.
def nat.fsum (f : ℕ → ℚ) : ℕ → ℚ | 0 := 0 | (n+1) := n.fsum + f n

constant σ : ℕ → Policy
constant σ_all : (ℕ → Policy) × list (ℕ → Policy)
constant Policy.update_at_infosets : Policy → list Infoset → Policy → Policy

constant Player : Type
constant utility : Player → Policy → Infoset → ℚ
constant D : Infoset → list Infoset
constant Succ : Player → Infoset → list Infoset

constant path : Player → Policy → rat
constant path_is_probability : ∀ i σ, 0 <= path i σ ∧ path i σ <= 1
constant opposite_player : Player → Player

def R.template (update_policy : Policy → Infoset → Policy → Policy) 
    (i : Player) (T : ℕ) (I : Infoset) : ℚ := 
    1 / T * 
    maximize σ_all (fun σ',
        T.fsum (fun t,
            let (σ, σ') := (σ t, σ' t) in
            let σ' := update_policy σ' I σ in
            path (opposite_player i) σ * (utility i σ' I - utility i σ I)
            )
        )
        
def R.full := R.template (fun σ' I σ, σ.update_at_infosets (D I) σ')
def R.full.pos (i : Player) (T : ℕ) (I : Infoset) := max (R.full i T I) 0
def R.immediate := R.template (fun σ' I σ, σ.update_at_infosets [I] σ')
def R.immediate.pos (i : Player) (T : ℕ) (I : Infoset) := max (R.immediate i T I) 0

lemma five (i : Player) (T : ℕ) (I : Infoset) 
        : R.full i T I <= R.immediate i T I + (Succ i I).fsum (fun I', R.full.pos i T I) := 
    sorry
    