import data.rat data.vector

def nat.foldl.fin_template {α : nat → Type*} (n' : nat) 
    : ∀ (n : fin n') (s : α 0) (f : ∀ (n : fin n'), (α n.val) → α (n.val+1)), α n.val
| ⟨0, _⟩ s f := s
| ⟨n+1, lt⟩ s f := let n' : fin n' := ⟨n, buffer.lt_aux_1 lt ⟩ in f n' (nat.foldl.fin_template n' s f)

def nat.foldl.fin {α : nat → Type*} 
    : ∀ (n : nat) (s : α 0) (f : ∀ (n : fin n), (α n.val) → α (n.val+1)), α n
| 0 s f := s
| (n+1) s f := 
    let n' : fin (n+1) := ⟨ n, lt_add_one n ⟩ in
    f n' (nat.foldl.fin_template (n+1) n' s f)

def Infoset := ℕ 
@[derive [has_lt, has_zero]] def Size := ℕ
@[derive [has_neg, has_one]] def Player := ℤ

inductive GameTree (infoset_sizes : Infoset → Size)
| Terminal (reward : ℚ) : GameTree
| Response (id : Infoset) (subnodes : fin (infoset_sizes id) → GameTree) : GameTree

def policy_sum {n : ℕ} (f : fin n → ℚ) : ℚ := @nat.foldl.fin (fun i, ℚ) n 0 (fun i s, s + f i)

structure Policy (infoset_sizes : Infoset → Size) := 
    (val : ∀ (id : Infoset), fin (infoset_sizes id) → ℚ)
    (wf : ∀ (id : Infoset), 0 < infoset_sizes id → policy_sum (val id) = 1 ∧ ∀ (i : fin (infoset_sizes id)), 0 <= val id i ∧ val id i <= 1)

variable {infoset_sizes : Infoset → Size}

-- Calculates the utilities directly.
def u.dive (σ : Policy infoset_sizes) : GameTree infoset_sizes → ℚ
| (GameTree.Terminal _ reward) := reward
| (GameTree.Response id' subnodes) :=
    let σ := σ.val id' in
    @nat.foldl.fin (fun i, rat) (infoset_sizes id') 0 (fun i s, s + σ i * u.dive (subnodes i))

-- Ignores the utilities of nodes that do not match.
def u.template (p : Player) (σ : Policy infoset_sizes) (id : Infoset) : Player → GameTree infoset_sizes → ℚ
| p' (GameTree.Terminal _ reward) := 0
| p' (GameTree.Response id' subnodes) := 
    if p = p' ∧ id = id' then
        let σ' := σ.val id' in
        @nat.foldl.fin (fun i, rat) (infoset_sizes id') 0 $ fun i s, s + σ' i * u.dive σ (subnodes i)
    else 
        @nat.foldl.fin (fun i, rat) (infoset_sizes id') 0 $ fun i s, s + u.template (-p') (subnodes i)
            
-- By partially applying u, it would be possible to get the same form as in the paper
def u (tree : GameTree infoset_sizes) (p : Player) (σ : Policy infoset_sizes) (id : Infoset) : ℚ := u.template p σ id 1 tree

inductive Fin : ℕ → Type
| zero : ∀ {n : ℕ}, Fin (n+1)
| suc : ∀ {n : ℕ} (i : Fin n), Fin (n+1)

inductive Vec (α : Type) : ℕ → Type
| nil : ∀ {n : ℕ}, Vec n 
| cons : ∀ {n : ℕ}, α → Vec n → Vec (n + 1)

inductive GameTree' (infoset_sizes : Infoset → Size)
| Terminal (reward : ℚ) : GameTree'
| Response (id : Infoset) (subnodes : Vec GameTree' (infoset_sizes id)) : GameTree'