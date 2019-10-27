import data.rat

private def array.init.template {α : Type*} (f : nat -> α) 
    : ∀ (up down : nat) (ar : array down α), array (down + up + 1) α 
| 0 down ar := ar.push_back (f down)
| (up + 1) down ar := 
    by {
        have : down + (up + 1) + 1 = down + 1 + up + 1, by ring,
        rw this,
        from array.init.template up (down+1) (ar.push_back (f down))
    }

def array.init {α : Type*} (i : nat) (f : nat -> α) : array i α :=
    match i with
    | 0 := array.nil
    | (i + 1) :=
        by { 
            have := array.init.template f i 0 array.nil,
            simp at this,
            from this
        }
    end

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

def array.sum {α : Type*} [has_zero α] [has_add α] {n : nat} (a : array n α) :=
    @nat.foldl.fin (fun _, α) n 0 (fun i s, a.read i + s)

def array.map_foldl {α β χ : Type*} {n : nat} (a : array n α) (f : α → β → χ × β) (s : β) : array n χ × β :=
    @nat.foldl.fin (fun n, array n χ × β) n (array.nil, s) 
        (fun (i : fin n) ⟨ a' , s ⟩, 
            let (el, s) := f (a.read i) s in 
            (a'.push_back el, s)
            )

def memoize.template {α : Type*} (n : nat) (p : fin n → option α): option α :=
    @nat.foldl.fin (fun i, option α) n none (fun i s, match s with none := p i | _ := s end)

def memoize {α : Type*} {β : α → Type*} [decidable_eq α] 
        (m : buffer (Σ α, β α )) (f : ∀ (k : α), β k) (k : α) : nat × β k × buffer (Σ α, β α) :=
    match @memoize.template (nat × β k × buffer (Σ α, β α)) m.1 (fun i, 
        let x := m.read i in
        if h : x.1 = k then by { have := x.2, rw h at this, exact some ⟨ i, this, m ⟩ }
        else none
        ) with
    | (some s) := s
    | none := let x := f k in ⟨ m.size, x, m.push_back ⟨ k, x ⟩ ⟩
    end

def Actions (𝔸 : Type*) := Σ (n : nat), fin n → 𝔸
def HistoryToActions (ℍ : Type*) (𝔸 : ℍ → Type*) := ∀ (h : ℍ), Actions (𝔸 h)

def actions_get {𝔸 : Type*} (actions : Actions 𝔸)
        : array actions.1 𝔸 :=
    let ⟨ actions_num, actions_fun ⟩ := actions in
    @nat.foldl.fin (fun n, array n 𝔸) actions_num array.nil
        (fun i a, a.push_back (actions_fun i))

def actions_map {𝔸 β : Type*} (actions : Actions 𝔸)  
        (f : 𝔸 → β)
        : array actions.1 β :=
    let ⟨ actions_num, actions_fun ⟩ := actions in
    @nat.foldl.fin (fun n, array n β) actions_num array.nil
        (fun i a, a.push_back (f (actions_fun i)))

def actions_foldl {𝔸 σ : Type*} (actions : Actions 𝔸)  
        (s : σ) (f : 𝔸 → σ → σ)
        : σ :=
    let ⟨ actions_num, actions_fun ⟩ := actions in
    @nat.foldl.fin (fun n, σ) actions_num s
        (fun i s, f (actions_fun i) s)

def actions_map_foldl {𝔸 β σ : Type*} (actions : Actions 𝔸)  
        (s : σ) (f : 𝔸 → σ → β × σ)
        : array actions.1 β × σ :=
    let ⟨ actions_num, actions_fun ⟩ := actions in
    @nat.foldl.fin (fun n, array n β × σ) actions_num (array.nil, s)
        (fun i ⟨ a , s ⟩, 
            let ⟨ el, s ⟩ := f (actions_fun i) s in
            ⟨ a.push_back el, s ⟩
            )

def actions_map_foldl2 {𝔸 β χ σ : Type*} 
        {n : nat}
        (actions : fin n → 𝔸) (ar : array n β)
        (s : σ) (f : 𝔸 → β → σ → χ × σ)
        : array n χ × σ :=
    @nat.foldl.fin (fun n, array n χ × σ) n (array.nil, s)
        (fun i ⟨ a , s ⟩, 
            let ⟨ el, s ⟩ := f (actions i) (ar.read i) s in
            ⟨ a.push_back el, s ⟩
            )

def buffer.attach_index {α : Type*} (a : buffer α) : buffer {i // ∃ v, a.read i = v} :=
    a.iterate buffer.nil (fun i _ s, s.push_back ⟨ i, ⟨ a.read i, rfl ⟩ ⟩)