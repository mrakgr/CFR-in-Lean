import helpers

def regret_match {n : nat} (a : array n rat) :=
    let sum := a.foldl 0 (fun a s, max a 0 + s) in
    if sum = 0 then have v : rat, from 1 / n, array.init n (fun _, v)
    else a.map (fun a, max a 0 / sum)

structure Node {𝔸 : Type*} (actions : Σ (n : nat), fin n → 𝔸) := mk :: 
    (strategy_sum : array actions.1 rat) 
    (regret_sum : array actions.1 rat)

def Infosets {ℍ 𝔸 : Type*} [lt : has_lt ℍ] (ha : HistoryToActions ℍ 𝔸) 
    := drbmap ℍ (Node ∘ ha) lt.lt

def Node_from_actions {𝔸 : Type*} (actions : Actions 𝔸) := 
    {Node . 
        strategy_sum := array.init actions.1 (fun _, 0), 
        regret_sum := array.init actions.1 (fun _, 0)
        }

def response {ℍ 𝔸 : Type*} [lt : has_lt ℍ] [decidable_rel lt.lt]
        (ha : HistoryToActions ℍ 𝔸)
        (is_updateable : bool) (one_probability two_probability : rat) (h : ℍ)
        (next : 𝔸 → rat → state (Infosets ha) rat)
        : state (Infosets ha) rat := ⟨ fun infosets,
    let (⟨ h' , node⟩ , infosets) := memoize infosets (fun h, Node_from_actions $ ha h) h in
    let action_probability := regret_match node.regret_sum in
    let ⟨ action_utility, infosets ⟩ := 
        actions_map_foldl2 (ha h').2 action_probability 
            infosets (fun action action_probability infosets, 
                if action_probability = 0 ∧ two_probability = 0 then (0, infosets) -- the pruning optimization
                else (next action (one_probability * action_probability)).run infosets
                ) in
    let action_utility_weighted_sum := 
        @nat.foldl.fin (fun i, rat) (ha h').1 0 
            (fun i s, s + action_utility.read i * action_probability.read i) in
    let infosets := 
        match is_updateable with
        | tt := 
            let add (f : ℚ → ℚ) (a b : array (ha h').1 ℚ) := array.map₂ (fun s x, s + f x) a b in 
            infosets.insert h' {
                strategy_sum := add (fun action_probability, one_probability * action_probability) node.strategy_sum action_probability,
                regret_sum := add (fun action_utility, two_probability * (action_utility - action_utility_weighted_sum)) node.regret_sum action_utility
                }
        | ff := infosets
        end in

    (-action_utility_weighted_sum, infosets)
    ⟩

def chance {ℍ 𝔸 Δ : Type*} [has_lt ℍ]
        (ha : HistoryToActions ℍ 𝔸) 
        (dice : Σ n, fin n → rat × Δ)
        (one_probability : rat) 
        (next : Δ → rat → state (Infosets ha) rat)
        : state (Infosets ha) rat := ⟨ fun infosets, 
    actions_foldl dice ((0 : rat), infosets) (
        fun ⟨ dice_probability, dice⟩ ⟨ util_sum, infosets ⟩ , 
            let (util, infosets) := (next dice (one_probability * dice_probability)).run infosets in
            (util_sum + util * dice_probability, infosets)
        )
    ⟩ 

def chance_uniform {ℍ 𝔸 Δ : Type*} [has_lt ℍ]
        (ha : HistoryToActions ℍ 𝔸) 
        (dice : Actions Δ)
        (one_probability : rat) 
        (next : Δ → rat → state (Infosets ha) rat)
        : state (Infosets ha) rat :=
    let dice_probability := 1 / dice.1 in
    chance ha ⟨ dice.1 , fun i, ⟨ dice_probability, dice.2 i ⟩ ⟩ one_probability next

def terminal {ℍ 𝔸 : Type*} [has_lt ℍ]
        (ha : HistoryToActions ℍ 𝔸)
        (reward : rat)
        : state (Infosets ha) rat := pure reward