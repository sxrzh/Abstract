import Mathlib
import Abstract.Group.Defs

namespace Abstract

@[simp] lemma unit_mul {α : Type} [Monoid α] (a : α) : (1 : α) * a = a :=
  (Monoid.unit_def a).1
@[simp] lemma mul_unit {α : Type} [Monoid α] (a : α) : a * (1 : α) = a :=
  (Monoid.unit_def a).2
@[simp] lemma inv_mul_eq_unit {α : Type} [Group α] (a : α) : a⁻¹ * a = 1 :=
  (Group.inv_def a).1
@[simp] lemma mul_inv_eq_unit {α : Type} [Group α] (a : α) : a * a⁻¹ = 1 :=
  (Group.inv_def a).2

lemma left_unit_is_unit {α : Type} [Group α] (e : α) (h : ∀ a, e * a = a) : e = 1 := by
  calc e = e * (1 : α) := by simp
       _ = 1 := h 1

lemma right_unit_is_unit {α : Type} [Group α] (e : α) (h : ∀ a, a * e = a) : e = 1 := by
  calc e = (1 : α) * e := by simp
       _ = 1 := h 1

@[simp] lemma left_unit_iff_unit {α : Type} [Group α] (e : α) : (∀ a, e * a = a) ↔ e = 1 := by
  constructor
  · intro h
    apply left_unit_is_unit
    exact h
  · intro h
    simp [h]

@[simp] lemma right_unit_iff_unit {α : Type} [Group α] (e : α) : (∀ a, a * e = a) ↔ e = 1 := by
  constructor
  · intro h
    apply right_unit_is_unit
    exact h
  · intro h
    simp [h]

lemma left_inv_is_inv {α : Type} [Group α] (a b : α) (h : b * a = 1) : b = a⁻¹ := by
  calc b = b * (a * a⁻¹) := by simp
       _ = (b * a) * a⁻¹ := by rw [mul_assoc]
       _ = a⁻¹ := by simp[h]

lemma right_inv_is_inv {α : Type} [Group α] (a b : α) (h : a * b = 1) : b = a⁻¹ := by
  calc b = (a⁻¹ * a) * b := by simp
       _ = a⁻¹ * (a * b) := by rw [mul_assoc]
       _ = a⁻¹ := by simp[h]

@[simp] lemma left_inv_iff_inv {α : Type} [Group α] (a b : α) : (b * a = 1) ↔ b = a⁻¹ := by
  constructor
  · intro h
    apply left_inv_is_inv
    exact h
  · intro h
    simp [h]

@[simp] lemma right_inv_iff_inv {α : Type} [Group α] (a b : α) : (a * b = 1) ↔ b = a⁻¹ := by
  constructor
  · intro h
    apply right_inv_is_inv
    exact h
  · intro h
    simp [h]

@[simp] lemma inv_inv {α : Type} [Group α] (a : α) : (a⁻¹)⁻¹ = a := by
  symm
  rw [← right_inv_iff_inv]
  simp

@[simp] lemma inv_eq_inv_iff {α : Type} [Group α] (a b : α) : a⁻¹ = b⁻¹ ↔ a = b := by
  constructor
  <;> intro h
  · have : (a⁻¹)⁻¹ = (b⁻¹)⁻¹ := by rw [h]
    repeat rw [inv_inv] at this
    exact this
  · rw [h]

@[simp] lemma inv_mul {α : Type} [Group α] (a b : α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  symm
  rw [← left_inv_iff_inv]
  calc b⁻¹ * a⁻¹ * (a * b) = b⁻¹ * (a⁻¹ * a) * b := by simp only [mul_assoc]
       _ = b⁻¹ * b := by simp
       _ = 1 := by simp

lemma unique_solution_left {α : Type} [Group α] (a b : α) : ∃! x, a * x = b := by
  use a⁻¹ * b
  constructor
  · simp [← mul_assoc]
  · intro y h
    have : a⁻¹ * a * y = a⁻¹ * b := by rw [mul_assoc, h]
    simp only [inv_mul_eq_unit, unit_mul] at this
    exact this

lemma unique_solution_right {α : Type} [Group α] (a b : α) : ∃! x, x * a = b := by
  use b * a⁻¹
  constructor
  · simp
  · intro y h
    have :  y * a * a⁻¹ = b * a⁻¹ := by rw [h]
    simp only [mul_assoc, mul_inv_eq_unit, mul_unit] at this
    exact this

@[simp] lemma right_cancel {α : Type} [Group α] (a b u : α) : a * u = b * u ↔ a = b := by
  constructor
  · intro h
    calc a = a * u * u⁻¹ := by simp
         _ = b * u * u⁻¹ := by rw [h]
         _ = b := by simp
  · intro h
    rw [h]

@[simp] lemma left_cancel {α : Type} [Group α] (a b u : α) : u * a = u * b ↔ a = b := by
  constructor
  · intro h
    calc a = u⁻¹ * u * a := by simp
         _ = u⁻¹ * (u * a) := by rw [Semigroup.mul_assoc]
         _ = u⁻¹ * (u * b) := by rw [h]
         _ = u⁻¹ * u * b := by rw [Semigroup.mul_assoc]
         _ = b := by simp
  · intro h
    rw [h]

@[simp] lemma inv_unit {α : Type} [Group α] : (1 : α)⁻¹ = 1 := by
  symm
  apply left_inv_is_inv
  simp

end Abstract
