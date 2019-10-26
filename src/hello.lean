import data.buffer

def array.find_index {α} {n} (arr : array n α) (p : α → Prop) [decidable_pred p] : option (fin n) :=
    arr.iterate none (λ i a o, o <|> if p a then some i else none)

def memoize {α : Type*} {β : α → Type*} [decidable_eq α] 
        (m : buffer (Σ α, β α )) (f : ∀ (k : α), β k) (k : α) : β k × buffer (Σ α, β α) :=
    match m.2.find_index (fun a, a.1 = k) with
    | (some i) := let x := m.read i in ⟨ x.2, m ⟩
    | none := let x := f k in ⟨ x, m.push_back ⟨ k, x ⟩ ⟩
    end