import data.rat

-- `constant`s are axiomatic definitions. They are inherently noncomputable.
constant Infoset : Type
constant Policy : Type

def maximize {α : Type} : α × list α → (α → ℚ) → ℚ | (x,xs) f := xs.foldl (fun s a, max s (f a)) (f x)
def list.fsum {α : Type} : (α → ℚ) → list α → ℚ | f l := l.foldl (fun s a, s + f a) 0

constant Infoset.fsum :  (Infoset → ℚ) → Infoset → ℚ
-- Compared to the paper, here I am moving the indexing so it obeys the C notation.
def nat.fsum (f : ℕ → ℚ) : ℕ → ℚ | 0 := 0 | (n+1) := n.fsum + f n

constant σ : ℕ → Policy
constant σ_all : (ℕ → Policy) × list (ℕ → Policy)
constant Policy.at : Policy → Infoset → Policy → Policy

constant Player : Type
constant u : Player → Policy → Infoset → ℚ
constant D : Infoset → Infoset
constant Succ : Player → Infoset → Infoset
constant SuccA : Player → Infoset → Policy → Infoset

constant π : Player → Policy → Infoset → ℚ
constant π_is_probability : ∀ i σ I, 0 <= π i σ I ∧ π i σ I <= 1
constant neg : Player → Player

def R.template (update_policy : Policy → Infoset → Policy → Policy) 
    (i : Player) (T : ℕ) (I : Infoset) : ℚ := 
    let u := u i in
    1 / T * 
    maximize σ_all (fun σ',
        T.fsum (fun t,
            let (σ, σ') := (σ t, σ' t) in
            let σ' := update_policy σ' I σ in
            π (neg i) σ I * (u σ' I - u σ I)
            )
        )
        
def R.full := R.template (fun σ' I σ, σ.at (D I) σ')
def R.full.pos (i : Player) (T : ℕ) (I : Infoset) := max (R.full i T I) 0
def R.imm := R.template (fun σ' I σ, σ.at I σ')
def R.imm.pos (i : Player) (T : ℕ) (I : Infoset) := max (R.imm i T I) 0

constant A : Infoset → Policy × list Policy
constant succ : Player → Policy → Infoset → Policy → Infoset → rat
constant succ_is_probability : ∀ i σ I a I', 0 <= succ i σ I a I' ∧ succ i σ I a I' <= 1

def R.full.expanded (i : Player) (T : ℕ) (I : Infoset) : ℚ := 
    let u := u i in
    1 / T * (maximize (A I) $ fun a, maximize σ_all $ fun σ', T.fsum $ fun t, 
        let (σ, σ') := (σ t, σ' t) in
        π (neg i) σ I * (u (σ.at I a) I - u σ I + (Succ i I).fsum (fun I', succ i σ I a I' * (u (σ.at (D I) σ') I' - u σ I')))
        )

constant Rfull_eq_expanded (i : Player) (T : ℕ) (I : Infoset) : R.full i T I = R.full.expanded i T I

lemma five (i : Player) (T : ℕ) (I : Infoset) 
        : R.full i T I <= R.imm i T I + (Succ i I).fsum (fun I', R.full.pos i T I) := 
    let u := u i in
    calc
        R.full i T I = R.full.expanded i T I : Rfull_eq_expanded i T I
        ... <= 
            1 / T * (maximize (A I) $ fun a, maximize σ_all $ fun σ', T.fsum $ fun t, 
                let (σ, σ') := (σ t, σ' t) in
                π (neg i) σ I * (u (σ.at I a) I - u σ I)
                ) 
            + 1 / T * (maximize (A I) $ fun a, maximize σ_all $ fun σ', T.fsum $ fun t, 
                let (σ, σ') := (σ t, σ' t) in
                π (neg i) σ I * (SuccA i I a).fsum (fun I', succ i σ I a I' * (u (σ.at (D I) σ') I' - u σ I'))
                ) : sorry
        ... =
            R.imm i T I + 1 / T * (maximize (A I) $ fun a, maximize σ_all $ fun σ', T.fsum $ fun t, 
                let (σ, σ') := (σ t, σ' t) in
                (SuccA i I a).fsum (fun I', π (neg i) σ I * succ i σ I a I' * (u (σ.at (D I') σ') I' - u σ I'))
                ) : sorry
        ... = 
            R.imm i T I + (maximize (A I) $ fun a, (SuccA i I a).fsum $ fun I', 
                1 / T * (maximize (A I) $ fun a, maximize σ_all $ fun σ', T.fsum $ fun t, 
                    let (σ, σ') := (σ t, σ' t) in
                    π (neg i) σ I * succ i σ I a I' * (u (σ.at (D I') σ') I' - u σ I')
                    ) 
                ) : sorry
        ... = R.imm i T I + (maximize (A I) $ fun a, (SuccA i I a).fsum $ fun I', R.full i T I') : sorry
        ... <= R.imm i T I + (Succ i I).fsum (fun I', R.full.pos i T I) : sorry
    
lemma six (i : Player) (T : ℕ) (I : Infoset) : R.full i T I <= (D I).fsum (fun I', R.full.pos i T I') :=
    calc 
        R.full i T I <= R.imm i T I + ((Succ i I).fsum $ fun I', (Succ i I').fsum $ fun I'', R.full.pos i T I'') : sorry
        ... <= R.imm.pos i T I + ((Succ i I).fsum $ fun I', (Succ i I').fsum $ fun I'', R.full.pos i T I'') : sorry
        ... <= (D I).fsum (fun I', R.full.pos i T I') : sorry