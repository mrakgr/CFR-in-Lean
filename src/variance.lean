import data.rat

variable (α : Type)

theorem list.eq.identity : ∀ (l : list α), list.map id l = l
    | [] := rfl
    | (x :: l) := by simp [list.eq.identity l]

def mean (l : list rat) : rat := list.sum l / l.length
@[simp] def sqr (x : rat) := x ^ 2
theorem sqr.eq.a_minus_b (a b : rat) : sqr (a - b) = sqr a - 2 * a * b + sqr b := by {unfold sqr, ring}

def E (f : rat -> rat) (l : list rat) := mean $ list.map f l

def var (l : list rat) (m : rat) := E (fun x, (x - m) ^ 2) l
def var' (l : list rat) (m : rat) := mean (list.map sqr l) - sqr m

theorem list.eq.sum_add (f g : rat → rat) : 
        ∀ (l : list rat), list.sum (list.map (λ x, f x + g x) l) = list.sum (list.map f l) + list.sum (list.map g l)
    | [] := rfl
    | (x :: l) := by simp [list.eq.sum_add]

theorem list.eq.sum_sub (f g : rat → rat) : 
        ∀ (l : list rat), list.sum (list.map (λ x, f x - g x) l) = list.sum (list.map f l) - list.sum (list.map g l)
    | [] := rfl
    | (x :: l) := by { 
        have := list.eq.sum_sub l,
        simp [list.eq.sum_add] at ⊢ this, 
        assumption
        }

theorem list.eq.sum_mul (c : rat) (f : rat → rat) : 
        ∀ (l : list rat), list.sum (list.map (λ x, c * f x) l) = c * list.sum (list.map f l)
    | [] := by simp
    | (x :: l) := by { simp, rw list.eq.sum_mul, ring }

theorem E.add {f g : rat -> rat} (l : list rat) : E (fun x, f x + g x) l = E f l + E g l :=
    by { unfold E mean, simp only [list.length_map, list.eq.sum_add], ring }

theorem E.sub {f g : rat -> rat} (l : list rat) : E (fun x, f x - g x) l = E f l - E g l :=
    by { unfold E mean, simp only [list.length_map, list.eq.sum_sub], ring }

theorem E.const_left {f : rat -> rat} (c : rat) (l : list rat) : E (fun x, c * f x) l = c * E f l :=
    by { simp [E, mean], rw [list.eq.sum_mul], ring }

theorem rat.eq.mult_elim (n : rat) :  n / n = 1 ∨ n = 0 :=
    if h : n = 0 then or.inr h
    else or.inl $ div_self h

theorem list.eq.repeat (c : rat) (l : list rat) : list.sum (list.map (fun _, c) l) = c * list.length l :=
    by { simp, rw add_monoid.smul_eq_mul _ c, ring }

theorem E.const_none (c : rat) : ∀ (x : rat) (l : list rat), E (fun x, c) (x :: l) = c
    | x l := 
        by {
            simp only [E, mean],
            rw list.eq.repeat,
            rw list.length_map,
            simp,
            from match rat.eq.mult_elim (1 + ↑(list.length l)) with
            | or.inl is_one := by { 
                have := congr_arg (fun x, c * x) is_one, 
                simp at this,
                ring at ⊢ this,
                assumption
                }
            | or.inr is_zero := by {
                ring at is_zero,
                norm_cast at is_zero
            }
            end
        }
    
theorem E.const_right (c : rat) (l : list rat) : E (fun x, x * c) l = E id l * c :=
    calc
        E (fun x, x * c) l = E (fun x, c * x) l : by simp [mul_comm]
        ... = c * E id l : by rw ← E.const_left; refl
        ... = E id l * c : by rw mul_comm

theorem E.const_both (c c' : rat) (l : list rat) : E (fun x, c * x * c') l = c * E id l * c' :=
    calc
        E (fun x, c * x * c') l = E (fun x, c * (x * c')) l : by simp [mul_assoc]
        ... = c * E (fun x, x * c') l : by rw E.const_left
        ... = c * (E id l * c') : by rw E.const_right
        ... = c * E id l * c' : by rw ← mul_assoc

theorem E.identity_is_mean (l : list rat) : E id l = mean l :=
    calc
        E id l = mean (list.map id l) : by unfold E
        ... = mean l : by rw list.eq.identity

theorem E.sqr_split (m : rat) (x : rat) (xs : list rat) : E (fun x, (x - m) ^ 2) (x :: xs) = E (fun x, x ^ 2) (x :: xs) - 2 * mean (x :: xs) * m + m ^ 2 :=
    let l := x :: xs in
    calc 
        E (fun x, (x - m) ^ 2) l = E (fun x, x ^ 2 - 2 * x * m + m ^ 2) l : by ring
        ... = E (fun x, x ^ 2) l - E (fun x, 2 * x * m) l + E (fun _, m ^ 2) l : by rw [E.add, E.sub]
        ... = E (fun x, x ^ 2) l - 2 * E id l * m + m ^ 2 : by rw [E.const_both, E.const_none]
        ... = E (fun x, x ^ 2) l - 2 * mean l * m + m ^ 2 : by rw [E.identity_is_mean]

theorem var_equals_var' : ∀ (l : list rat), var l (mean l) = var' l (mean l) 
    | [] := rfl
    | l@(x :: xs) := 
        let m := mean l in
        calc
            var l m = E (fun x, (x - m) ^ 2) l : by unfold var
            ... = E (fun x, x ^ 2) l - 2 * m * m + m ^ 2 : by rw E.sqr_split
            ... = E (fun x, x ^ 2) l - 2 * (m * m) + m ^ 2 : by rw [mul_assoc]
            ... = E (fun x, x ^ 2) l - 2 * m ^ 2 + m ^ 2 : by ring
            ... = E (fun x, x ^ 2) l - m ^ 2 : by ring
            ... = var' l m : by refl

-- Is also known as MSE = variance + bias ^ 2 proof
theorem mean_is_global_minima_of_variance (m' : rat) : ∀ (l : list rat), var l (mean l) <= var l m'
    | [] := by simp [var]
    | l@(x :: xs) := 
        let m := mean l in
        calc 
            var l m = E (fun x, (x - m) ^ 2) l : rfl
            ... = E (fun x, x ^ 2) l - 2 * m * m + m ^ 2 : by rw E.sqr_split
            ... <= E (fun x, x ^ 2) l - 2 * m * m' + m' ^ 2 : by { repeat {rw [sub_eq_add_neg, add_assoc]}, apply add_le_add_left, apply @le_of_add_le_add_right _ _ _ (m ^ 2), convert (pow_two_nonneg (m - m')); ring }
            ... = E (fun x, (x - m') ^ 2) l : by rw ← E.sqr_split
            ... = var l m' : rfl