import Mathlib.Tactic
-- imports all the Lean tactics
import Mathlib.Order.Filter.Basic

variable {α : Type}
variable (p q r : Prop)

open Filter Set
-- so we don't keep having to type `Filter.le_def` and `Set.Subset.trans` etc

open scoped Filter

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
