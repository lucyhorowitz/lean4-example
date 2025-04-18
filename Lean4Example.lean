import Mathlib.Tactic
-- imports all the Lean tactics
import Mathlib.Order.Filter.Basic

open Nat
open Function

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

inductive X : Type
  | a : X

-- in fact the term of type X is called `X.a`.
-- Let Y be {b,c}
inductive Y : Type
  | b : Y
  | c : Y

inductive Z : Type
  | d : Z

def f : X → Y
  | X.a => Y.b

-- define g by g(Y.b)=g(Y.c)=Z.d
def g : Y → Z
  | Y.b => Z.d
  | Y.c => Z.d

theorem gf_injective : Injective (g ∘ f) := by
  rintro ⟨_⟩ ⟨_⟩ _
  rfl

theorem gYb_eq_gYc : g Y.b = g Y.c :=
  by-- they're both definitionally `Z.d`
  rfl

example : ¬∀ A B C : Type, ∀ (ψ1 : A → B) (ψ2 : B → C), Injective (ψ2 ∘ ψ1) → Injective ψ2 := by
  intro h
  specialize h X Y Z f g gf_injective gYb_eq_gYc
  cases h
