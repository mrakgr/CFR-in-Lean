import data.rat
import drbmap
def claims := list.to_buffer [(1,2), (1,3), (1,4), (1,5), (1,6), (1,1), (2,2), (2,3), (2,4), (2,5), (2,6), (2,1)]

def Actions (𝔸 : Type*) := Σ (n : nat), fin n → 𝔸
def HistoryToActions (ℍ 𝔸 : Type*) := ℍ → Actions 𝔸

def dice := list.to_buffer [1,2,3,4,5,6]
def History : Type* := {die // die ∈ dice} × list {i // ∃ v, claims.read i = v}

inductive Action
| Claim (claim : {i // ∃ v, claims.read i = v}) : Action
| Dudo : Action

def Infosets {ℍ 𝔸 : Type*} [lt : has_lt ℍ] (ha : HistoryToActions ℍ 𝔸) 
    := drbmap ℍ (Node ∘ ha) lt.lt

def ha : HistoryToActions History Action := sorry

structure Particle (α : Type*) := mk ::
    (infosets : Infosets ha)