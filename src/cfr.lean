import helpers

def regret_match {n : nat} (a : array n rat) :=
    let sum := a.foldl 0 (fun a s, max a 0 + s) in
    if sum = 0 then have v : rat, from 1 / n, array.init n (fun _, v)
    else a.map (fun a, max a 0 / sum)

structure Node {𝔸 : Type*} (actions : Σ (n : nat), fin n → 𝔸) := mk :: 
    (strategy_sum : array actions.1 rat) 
    (regret_sum : array actions.1 rat)

def Infosets {ℍ 𝔸 : Type*} [lt : has_lt ℍ]
        (actions : ∀ (h : ℍ), Σ action_count, fin action_count → 𝔸)
    := drbmap ℍ (Node ∘ actions) lt.lt

def Node_from_actions {𝔸 : Type*} (actions : Σ (n : nat), fin n → 𝔸) := 
    {Node . 
        strategy_sum := array.init actions.1 (fun _, 0), 
        regret_sum := array.init actions.1 (fun _, 0)
        }

def response {ℍ 𝔸 : Type*} [lt : has_lt ℍ] [decidable_rel lt.lt]
        (ha : ℍ → Σ (n : nat), fin n → 𝔸)
        (is_updateable : bool) (h : ℍ) (one_probability two_probability : rat) 
        (next : 𝔸 → rat → Infosets ha -> rat × Infosets ha) (infosets : Infosets ha) 
        : rat × Infosets ha :=
    let (⟨ h' , node⟩ , infosets) := memoize infosets (fun h, Node_from_actions $ ha h) h in
    let action_probability := regret_match node.regret_sum in
    let ⟨ action_utility, infosets ⟩ := 
        actions_map_foldl2 (ha h').2 action_probability 
            infosets (fun action action_probability infosets, 
                if action_probability = 0 ∧ two_probability = 0 then (0, infosets) -- the pruning optimization
                else next action (one_probability * action_probability) infosets
                ) in
    let action_utility_utility_weighted_sum := 
        @nat.foldl.fin (fun i, rat) (ha h').1 0 
            (fun i s, s + action_utility.read i * action_probability.read i) in
    let infosets := 
        match is_updateable with
        | tt := 
            let add (f : ℚ → ℚ) (a b : array (ha h').1 ℚ) := array.map₂ (fun s x, s + f x) a b in 
            infosets.insert h' {
                strategy_sum := add (fun action_probability, one_probability * action_probability) node.strategy_sum action_probability,
                regret_sum := add (fun action_utility, two_probability * (action_utility - action_utility_utility_weighted_sum)) node.regret_sum action_utility
                }
        | ff := infosets
        end in

    (-action_utility_utility_weighted_sum, infosets)
