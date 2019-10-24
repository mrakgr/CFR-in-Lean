prelude
import init.data.rbtree
import init.data.rbtree.basic tactic.library_search

universes u v w

def drbmap_lt {α : Type u} {β : α → Type v} (lt : α → α → Prop) (a b : Σ α, β α) : Prop :=
lt a.1 b.1

set_option auto_param.check_exists false

def drbmap (α : Type u) (β : α → Type v) (lt : α → α → Prop . rbtree.default_lt) : Type (max u v) :=
rbtree (Σ α, β α) (drbmap_lt lt)

def mk_drbmap (α : Type u) (β : α → Type v) (lt : α → α → Prop . rbtree.default_lt) : drbmap α β lt :=
mk_rbtree (Σ α, β α) (drbmap_lt lt)

namespace drbmap
variables {α : Type u} {β : α → Type v} {δ : Type w} {lt : α → α → Prop}

def empty (m : drbmap α β lt) : bool :=
m.empty

def to_list (m : drbmap α β lt) : list (Σ α, β α) :=
m.to_list

def min (m : drbmap α β lt) : option (Σ α, β α) :=
m.min

def max (m : drbmap α β lt) : option (Σ α, β α) :=
m.max

def fold (f : ∀ (a : α), β a → δ → δ) (m : drbmap α β lt) (d : δ) : δ :=
m.fold (λ e, f e.1 e.2) d

def rev_fold (f : ∀ (a : α), β a → δ → δ) (m : drbmap α β lt) (d : δ) : δ :=
m.rev_fold (λ e, f e.1 e.2) d

private def mem' (a : α) : ∀ (m : rbnode (Σ α, β α)), Prop
| rbnode.leaf           := false
| (rbnode.red_node l ⟨ v, _ ⟩  r)  := (¬ lt a v ∧ ¬ lt v a) ∨ mem' l ∨ mem' r
| (rbnode.black_node l ⟨ v, _ ⟩  r)  := (¬ lt a v ∧ ¬ lt v a) ∨ mem' l ∨ mem' r

def mem (k : α) (m : drbmap α β lt) : Prop := @mem' α β lt k m.val

instance : has_mem α (drbmap α β lt) := ⟨mem⟩

instance [has_repr (Σ α, β α)] : has_repr (drbmap α β lt) :=
⟨λ t, "drbmap_of " ++ repr t.to_list⟩

def drbmap_lt_dec [h : decidable_rel lt] : decidable_rel (@drbmap_lt α β lt) :=
λ a b, h a.1 b.1

variable [decidable_rel lt]

def insert (m : drbmap α β lt) (k : α) (v : β k) : drbmap α β lt :=
@rbtree.insert _ _ drbmap_lt_dec m ⟨ k, v ⟩

private def find (k : α) : rbnode (Σ α, β α) → option (Σ α, β α)
| rbnode.leaf             := none
| (rbnode.red_node a k' b) := 
    if lt k k'.1 then find a
    else if lt k'.1 k then find b
    else k'
| (rbnode.black_node a k' b) := 
    if lt k k'.1 then find a
    else if lt k'.1 k then find b
    else k'

def find_entry (m : drbmap α β lt) (k : α) : option (Σ α, β α) := @find _ _ lt _ k m.val

def contains (m : drbmap α β lt) (k : α) : bool :=
(find_entry m k).is_some

def from_list (l : list (Σ α, β α)) (lt : α → α → Prop . rbtree.default_lt) [decidable_rel lt] : drbmap α β lt :=
l.foldl (λ m p, insert m p.1 p.2)  (mk_drbmap α β lt)

end drbmap

def drbmap_of {α : Type u} {β : α → Type v} (l : list (Σ α, β α)) (lt : α → α → Prop . rbtree.default_lt) [decidable_rel lt] : drbmap α β lt :=
drbmap.from_list l lt
