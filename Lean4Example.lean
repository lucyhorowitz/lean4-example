import Mathlib.Tactic
-- imports all the Lean tactics
import Mathlib.Order.Filter.Basic

open Nat

variable {α : Type}
variable (p q r : Prop)

open Filter Set

open scoped Filter

theorem hello_world (a b c : Nat)
  : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b, ←add_assoc]

theorem foo (a : Nat) : a + 1 = Nat.succ a := by rfl

theorem test1 (S T : Set α) : 𝓟 S ≤ 𝓟 T ↔ S ⊆ T := by
  constructor
  · intro h
    rw [le_def] at h
    have hT : T ∈ 𝓟 T := mem_principal_self T
    specialize h T hT
    rwa [mem_principal] at h
  · intro hST
    rw [le_def]
    intro X hX
    rw [mem_principal] at hX ⊢
    exact Subset.trans hST hX

theorem test2 : (p ∧ q) → (p → q → r) → r := by
  intro h1 h2
  apply h2
  exact h1.1
  exact h1.2

theorem sorry_test : (p ∧ q) → (p → q → r) → r := by
  intro h1 h2
  apply h2
  sorry
  exact h1.2
