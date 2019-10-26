-- As it turns out,  these red black trees not being able to understand that the key 
-- being put in is the same as the one being taken out when doing indexing into them 
-- is a lot bigger problem than I thought at first. With dependent types, that means 
-- that it can no longer reduce based on the key and it is causing me all sorts of 
-- issues downstream.

-- These trees are useless as they are now. I'd recommend avoiding them in favor of 
-- something that uses direct equality.

-- Note, look into the previous commit for a completed version.
-- I'll leave this in a half baked state for the time being as I do not
-- know how to rewrite this to use trichotomnous comparison.

-- In particular, insertion requires a well foundedness proof related to the
-- standard comparison and I do not feel like spending time in order to thoroughly
-- get familiar with RB trees just so I can redesign them properly.

prelude
import init.data.rbtree
import init.data.rbtree.basic tactic.library_search

universes u v w

def drbmap_lt {α : Type u} {β : α → Type v} (lt : α → α → Prop) (a b : Σ α, β α) : Prop :=
lt a.1 b.1

set_option auto_param.check_exists false

def drbmap (α : Type u) [lt : has_lt α] [is_trichotomous α lt.lt] (β : α → Type v) : Type (max u v) :=
rbtree (Σ α, β α) (drbmap_lt lt.lt)

def mk_drbmap (α : Type u) [lt : has_lt α] [is_trichotomous α lt.lt] (β : α → Type v) : drbmap α β :=
mk_rbtree (Σ α, β α) (drbmap_lt lt.lt)

namespace drbmap

def empty {α : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt] 
    (m : drbmap α β) : bool :=
m.empty

def to_list {α : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt]
    (m : drbmap α β) : list (Σ α, β α) :=
m.to_list

def min {α : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt]
    (m : drbmap α β) : option (Σ α, β α) :=
m.min

def max {α : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt]
    (m : drbmap α β) : option (Σ α, β α) :=
m.max

def fold {α δ : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt]
    (f : ∀ (a : α), β a → δ → δ) (m : drbmap α β) (d : δ) : δ :=
m.fold (λ e, f e.1 e.2) d

def rev_fold {α δ : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt]
    (f : ∀ (a : α), β a → δ → δ) (m : drbmap α β) (d : δ) : δ :=
m.rev_fold (λ e, f e.1 e.2) d

private def mem' {α : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt]
    (a : α) : ∀ (m : rbnode (Σ α, β α)), Prop
| rbnode.leaf           := false
| (rbnode.red_node l ⟨ v, _ ⟩  r)  := a < v ∨ a = v ∨ a > v
| (rbnode.black_node l ⟨ v, _ ⟩  r)  := a < v ∨ a = v ∨ a > v

def mem {α : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt]
    (k : α) (m : drbmap α β) : Prop := mem' k m.val

instance {α : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt] : has_mem α (drbmap α β) := ⟨mem⟩

instance {α : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt] [has_repr (Σ α, β α)] : has_repr (drbmap α β) :=
⟨λ t, "drbmap_of " ++ repr t.to_list⟩

def insert {α : Type u} {β : α → Type v} [lt : has_lt α] [is_trichotomous α lt.lt] 
    (m : drbmap α β lt) (k : α) (v : β k) : drbmap α β lt :=
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