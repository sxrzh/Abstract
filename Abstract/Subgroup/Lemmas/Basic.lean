import Mathlib
import Abstract.Group.Basic
import Abstract.Subgroup.Defs

namespace Abstract

@[simp] lemma mul_mem {α : Type} [Group α] (H : Subgroup α) {a b : α} (ha : a ∈ H) (hb : b ∈ H) :
  a * b ∈ H := H.mul_mem a b ha hb
@[simp] lemma one_mem {α : Type} [Group α] (H : Subgroup α) :
  (1 : α) ∈ H := H.one_mem
@[simp] lemma inv_mem {α : Type} [Group α] (H : Subgroup α) {a : α} (ha : a ∈ H) :
  a⁻¹ ∈ H := H.inv_mem a ha

-- lemma subgroup_is_group {α : Type} [Group α] (S : Set α) :
--   Nonempty (Group S) := by
--   exact ⟨{
--     unit := (1 : α)
--     inv := _inv
--     inv_def := by
--       intro a
--       constructor
--       · exact h_linv a
--       · exact h_rinv a
--     unit_def := by
--       intro a
--       let a' := _inv a
--       constructor
--       · calc e * a = (a * a') * a := by rw [h_rinv a]
--              _ = a * (a' * a) := by simp
--              _ = a * e := by rw [h_linv a]
--              _ = a := by rw [h1]
--       · exact h1 a
--   }⟩

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
      apply mul_mem H ha (inv_mem H hb)
  · intro ⟨⟨x, hx⟩, hv⟩
    have one_mem' : 1 ∈ S := by
      rw [(by simp : 1 = x * x⁻¹)]
      exact hv x x hx hx
    have inv_mem' : ∀ a, a ∈ S → a⁻¹ ∈ S := by
      intro a ha
      have : (1 : α) * a⁻¹ ∈ S := hv 1 a one_mem' ha
      simp only [unit_mul] at this
      exact this
    have mul_mem' : ∀ a b, a ∈ S → b ∈ S → a * b ∈ S := by
      intro a b ha hb
      have hbi : b⁻¹ ∈ S := inv_mem' b hb
      have : a * (b⁻¹)⁻¹ ∈ S := hv a b⁻¹ ha hbi
      simp only [inv_inv] at this
      exact this
    let H : Subgroup α :=
    {
      carrier := S
      mul_mem {a b} := mul_mem' a b
      one_mem := one_mem'
      inv_mem {a} := inv_mem' a
    }
    use H

lemma finset_mul_mem_applies_inv_mem {α : Type} [Group α] (S : Finset α) :
  (∀ a b, a ∈ S → b ∈ S → a * b ∈ S) → ∀ a, a ∈ S → a⁻¹ ∈ S := by
  intro h a ha
  have h_pow: ∀ n : ℕ, n > 0 → a ^ n ∈ S := by
    intro n hn
    induction n with
    | zero => contradiction
    | succ n hp =>
      cases n with
      | zero => simp [ha]
      | succ n =>
        have : a ^ (n + 1) ∈ S := hp (by simp)
        rw [pown_succ]
        exact h _ _ this ha
  let n := Finset.card S
  let f := fun m ↦ a ^ m
  let T := Finset.Icc 1 (n + 1)
  have hf : ∀ n : ℕ, n > 0 → f n ∈ S := by apply h_pow
  have h_card : S.card < T.card := by simp [n, T]
  have : Set.MapsTo f T S := by
    intro t ht
    change t ∈ T at ht
    change a ^ t ∈ S
    apply h_pow
    exact (Finset.mem_Icc.mp ht).1
  have : ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ f x = f y :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card this
  rcases this with ⟨x, ⟨hx, ⟨y, ⟨hy, h_neq, h_eq⟩⟩⟩⟩
  simp only [pown_eq_pow, f] at h_eq
  have h_inv (x y : ℕ) (h_lt : y < x) (h_eq : a ^ x = a ^ y) : a⁻¹ ∈ S := by
    have h_comp : x ≥ y := by omega
    have h_comp_ : x > y := by omega
    have : a ^ (x - y) = 1 := by
      calc a ^ (x - y) = a ^ x * (a ^ y)⁻¹ := by rw [pown_sub _ _ _ (by omega)]
        _ = 1 := by simp [h_eq]
    have : a⁻¹ = a ^ (x - y - 1) := by
      calc a⁻¹ = (1 : α) * a⁻¹ := by simp
        _ = a ^ (x - y) * a⁻¹ := by rw [← this]
        _ = a ^ (x - y - 1) := by rw [pown_mul_inv a (x - y) (by omega)]
    rw [this]
    by_cases hh: x - y - 1 = 0
    · rw [hh, pown_zero] at this
      have ha1: a = 1 := by
        calc a = (a⁻¹)⁻¹ := by simp
          _ = 1⁻¹ := by rw [this]
          _ = 1 := by simp
      simp [hh, ←ha1, ha]
    · apply h_pow
      omega
  by_cases h_comp : x < y
  · apply h_inv y x (by omega) (by simp [h_eq])
  · exact h_inv x y (by omega) h_eq

lemma finset_subgroup_iff {α : Type} [Group α] (S : Finset α) :
  (∃ (H : Subgroup α), H.carrier = S) ↔
    Nonempty S ∧ ∀ a b, a ∈ S → b ∈ S → a * b ∈ S := by
  constructor
  · intro ⟨H, hCar⟩
    constructor
    · use 1
      have : 1 ∈ H := H.one_mem
      change 1 ∈ (S : Set α)
      rw [← hCar]
      exact this
    · intro a b ha hb
      change a ∈ (S : Set α) at ha
      change b ∈ (S : Set α) at hb
      change a * b ∈ (S : Set α)
      rw [← hCar] at ha hb ⊢
      change a ∈ H at ha
      change b ∈ H at hb
      change a * b ∈ H
      apply mul_mem H ha hb
  · intro ⟨⟨x, hx⟩, hv⟩
    have h_inv : ∀ a, a ∈ S → a⁻¹ ∈ S :=
      finset_mul_mem_applies_inv_mem S hv
    have h_one : 1 ∈ S := by
      rw [(by simp : 1 = x * x⁻¹)]
      exact hv _ _ hx (h_inv x hx)
    let H : Subgroup α :=
    {
      carrier := S
      mul_mem := hv
      one_mem := h_one
      inv_mem := h_inv
    }
    use H

end Abstract
