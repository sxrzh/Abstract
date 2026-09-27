import Mathlib
import Abstract.Group.Basic
import Abstract.Subgroup.Defs

namespace Abstract

@[simp] lemma mul_mem {α : Type} [Group α] (H : Subgroup α) {a b : α} (ha : a ∈ H) (hb : b ∈ H) :
  a * b ∈ H := H.mul_mem ha hb
@[simp] lemma one_mem {α : Type} [Group α] (H : Subgroup α) :
  (1 : α) ∈ H := H.one_mem
@[simp] lemma inv_mem {α : Type} [Group α] (H : Subgroup α) {a : α} (ha : a ∈ H) :
  a⁻¹ ∈ H := H.inv_mem ha

lemma subgroup_iff {α : Type} [Group α] (S : Set α) :
  (∃ (H : Subgroup α), H.carrier = S) ↔
    Nonempty S ∧ ∀ a b, a ∈ S → b ∈ S → a * b⁻¹ ∈ S := by
  constructor
  · intro ⟨H, hCar⟩
    constructor
    · use 1
      have : 1 ∈ H := H.one_mem
      rw [← hCar]
      exact this
    · intro a b ha hb
      rw [← hCar] at ha hb ⊢
      change a ∈ H at ha
      change b ∈ H at hb
      change a * b⁻¹ ∈ H
      apply H.mul_mem ha (H.inv_mem hb)
  · intro ⟨⟨x, hx⟩, h_valid⟩
    let H : Subgroup α where
      carrier := S
      one_mem := by sorry
      mul_mem := by sorry
      inv_mem := by sorry
    use H
    sorry

end Abstract
