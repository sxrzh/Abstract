import Mathlib
import Abstract.Group.Basic

namespace Abstract

structure Subsemigroup (α : Type) [Semigroup α] where
  carrier : Set α
  mul_mem : ∀ a b, a ∈ carrier → b ∈ carrier → a * b ∈ carrier

structure Submonoid (α : Type) [Monoid α] extends Subsemigroup α where
  one_mem : (1 : α) ∈ carrier

structure Subgroup (α : Type) [Group α] extends Submonoid α where
  inv_mem : ∀ a, a ∈ carrier → a⁻¹ ∈ carrier

instance {α : Type} [Group α] {H : Subgroup α} : Group H.carrier where
  mul := fun a b => ⟨a.1 * b.1, H.mul_mem a.1 b.1 a.2 b.2⟩
  mul_assoc := by intro a b c; ext; simp
  unit := ⟨1, H.one_mem⟩
  unit_def := by intro a; constructor <;> ext <;> simp
  inv := fun a => ⟨a.1⁻¹, H.inv_mem a.1 a.2⟩
  inv_def := by intro a; constructor <;> ext <;> simp

instance {α : Type} [Semigroup α] : SetLike (Subsemigroup α) α where
  coe s := s.carrier
  coe_injective p q h := by
    cases p
    cases q
    congr

instance {α : Type} [Monoid α] : SetLike (Submonoid α) α where
  coe s := s.carrier
  coe_injective p q h := by
    obtain ⟨⟨hp, _⟩, _⟩ := p
    obtain ⟨⟨hq, _⟩, _⟩ := q
    congr

instance {α : Type} [Group α] : SetLike (Subgroup α) α where
  coe s := s.carrier
  coe_injective p q h := by
    obtain ⟨⟨⟨hp, _⟩, _⟩, _⟩ := p
    obtain ⟨⟨⟨hq, _⟩, _⟩, _⟩ := q
    congr

instance lCoset {α : Type} [Group α] : HMul α (Subgroup α) (Set α) where
  hMul a H := (H : Set α).image (fun h ↦ a * h)

instance rCoset {α : Type} [Group α] : HMul (Subgroup α) α (Set α) where
  hMul H a := (H : Set α).image (fun h ↦ h * a)

def is_subgroup {α : Type} [Group α] (S : Set α) :=
  ∃ H : Subgroup α, H.carrier = S

def Center {α : Type} [Group α] : Set α :=
  setOf (fun x ↦ ∀ a : α, a * x = x * a)

end Abstract
