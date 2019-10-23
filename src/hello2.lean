def read {S : Type} : state S S :=
    ⟨ λ s, (s, s) ⟩

def write {S : Type} : S → state S unit :=
    fun s0, ⟨ fun s, ((), s0) ⟩ 

