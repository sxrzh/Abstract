import Mathlib
import Abstract.Group.Defs
import Abstract.Group.Lemmas.Basic

namespace Abstract

-- 2.1.5
example {α : Type} [Group α] (h : ∀ a : α, a⁻¹ = a) : Nonempty (AbelianGroup α) :=
  ⟨{
    mul_comm := by
      intro x y
      have h2 (a : α) : a * a = 1 := by simp [h]
      have : x * y * x * y = 1 := by
        calc x * y * x * y = (x * y) * (x * y) := by simp
          _ = (x * y) * (x * y)⁻¹ := by rw [h]
          _ = 1 := by rw [mul_inv_eq_unit]
      have : x * (x * y * x * y) * y = x * y := by
        rw [this, mul_unit]
      calc x * y = x * (x * y * x * y) * y := by rw [this]
        _ = (x * x) * (y * x) * (y * y) := by simp
        _ = y * x := by simp [h2]
  }⟩

-- 2.1.9
theorem runit_rinv_is_group {G : Type} [Semigroup G] (e : G) (h1 : ∀ a : G, a * e = a)
  (h2 : ∀ a : G, ∃ a' : G, a * a' = e) : Nonempty (Group G) := by
  let _inv := fun a => (h2 a).choose
  have h_rinv (a : G) : a * _inv a = e := (h2 a).choose_spec
  have h_linv (a : G) : _inv a * a = e := by
    let a' := _inv a
    let b := _inv a'
    have h_rinva : a * a' = e := h_rinv a
    have h_rinvb : a' * b = e := h_rinv a'
    change a' * a = e
    symm
    calc e = a' * b := by rw [h_rinvb]
         _ = a' * e * b := by rw [h1]
         _ = a' * (a * a') * b := by rw [h_rinva]
         _ = a' * a * (a' * b) := by simp
         _ = a' * a := by simp [h_rinvb, h1]
  exact ⟨{
    unit := e
    inv := _inv
    inv_def := by
      intro a
      constructor
      · exact h_linv a
      · exact h_rinv a
    unit_def := by
      intro a
      let a' := _inv a
      constructor
      · calc e * a = (a * a') * a := by rw [h_rinv a]
             _ = a * (a' * a) := by simp
             _ = a * e := by rw [h_linv a]
             _ = a := by rw [h1]
      · exact h1 a
  }⟩

-- 2.1.10
example {G : Type} [Nonempty G] [DecidableEq G] [Fintype G] [Semigroup G]
  (e : G) (h1 : ∀ a : G, a * e = a) (h2 : ∀ a b c : G, a * b = a * c → b = c)
  : Nonempty (Group G) := by
  have h_rinv_exists (a : G) : ∃ a', a * a' = e := by
    by_contra h_contra
    simp only [not_exists] at h_contra
    let G' := {x : G // x ≠ e}
    have h_card : Fintype.card G' < Fintype.card G :=
      Fintype.card_subtype_lt (x := e) (by simp)
    let trans : G → G' := fun t => ⟨a * t, h_contra t⟩
    have : ∃ x y, x ≠ y ∧ trans x = trans y :=
      Fintype.exists_ne_map_eq_of_card_lt trans h_card
    obtain ⟨x, y, ⟨h_ne, h_teq⟩⟩ := this
    have : a * x = a * y := by
      have h_val : (trans x).val = (trans y).val :=
        congr_arg Subtype.val h_teq
      simp only [trans] at h_val
      exact h_val
    apply (h2 a x y) at this
    contradiction
  exact runit_rinv_is_group e h1 h_rinv_exists

end Abstract
