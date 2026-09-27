import Mathlib
import Abstract.Group.Basic

namespace Abstract

structure Subsemigroup (α : Type) [Semigroup α] where
  carrier : Set α
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier

structure Submonoid (α : Type) [Monoid α] extends Subsemigroup α where
  one_mem : (1 : α) ∈ carrier

structure Subgroup (α : Type) [Group α] extends Submonoid α where
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier

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

open scoped Pointwise

/-
  Left coset is defined as a·H
-/


end Abstract
