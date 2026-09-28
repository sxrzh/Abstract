import Mathlib
import Abstract.Group.Basic
import Abstract.Subgroup.Defs
import Abstract.Subgroup.Lemmas.Basic

open Lean Elab Command

namespace Abstract
open scoped Pointwise

/-!
## `to_rcoset`

A command macro in the spirit of Mathlib's `to_additive`: it takes a declaration about
left cosets and automatically emits the corresponding declaration about right cosets.

The generated statement is obtained by *reversing every multiplication* — the left coset
`a * H` becomes the right coset `H * a`, and more generally `x * y` becomes `y * x`.
This is exactly the anti-automorphism `x ↦ x⁻¹` of the group, which sends the left coset
`a * H` to the right coset `H * a⁻¹`.  Identifiers are renamed along the same lines
(`lcoset ↦ rcoset`, and `left ↔ right`), so that references to the dual lemmas inside the
proof are picked up automatically.

The proof of the generated declaration is obtained by applying the same transformation to
the proof term of the source declaration, so it works out of the box for proofs that are
"structural" (definitional unfoldings, and rewrites through the dual lemmas).  A proof
that pushes group elements around by hand (e.g. via `mul_assoc`/`mul_mem` with a fixed
argument order) may still need a little manual adjustment — see `rcoset_eq_iff` below.
-/
namespace ToRcoset

/-- Rename a string: `lcoset ↦ rcoset` and swap `left`/`right`. -/
def renameString (s : String) : String :=
  let s := s.replace "lcoset" "\x01\x01coset"
  let s := s.replace "left" "right"
  let s := s.replace "right" "left"
  s.replace "\x01\x01coset" "rcoset"

/-- Rename every component of a name. -/
partial def renameName : Name → Name
  | .str p s => .str (renameName p) (renameString s)
  | .num p i => .num (renameName p) i
  | .anonymous => .anonymous

/-- A product `a * b` is represented as a node with three arguments `#[a, *, b]`. -/
def isMul (s : Syntax) : Bool :=
  s.getArgs.size == 3 &&
    (match s.getArgs[1]! with | .atom _ "*" => true | _ => false)

/-- Reverse every multiplication and rename lcoset-related identifiers. -/
partial def transform (s : Syntax) : Syntax :=
  match s with
  | .ident info raw val pre => .ident info raw (renameName val) pre
  | .node info k args =>
      if isMul s then
        .node info k #[transform args[2]!, args[1]!, transform args[0]!]
      else
        .node info k (args.map transform)
  | _ => s

end ToRcoset

/-- `to_rcoset <declaration>` elaborates `<declaration>` and, on top of it, its *rcoset
dual*: the statement with every multiplication reversed (`a * H` ↦ `H * a`) and every
`lcoset`/`left` renamed to `rcoset`/`right`, with the proof transformed in the same way. -/
elab "to_rcoset " c:command : command => do
  elabCommand c
  elabCommand (ToRcoset.transform c)

to_rcoset
@[simp] lemma in_lcoset_iff {α : Type} [Group α] {H : Subgroup α} {a b : α} :
  a ∈ b * H ↔ ∃ h, h ∈ H ∧ b * h = a := by
  dsimp [HMul.hMul]
  simp

to_rcoset
@[simp] lemma self_in_lcoset {α : Type} [Group α] {H : Subgroup α} {a : α} :
  a ∈ a * H := by
  rw [in_lcoset_iff]
  use 1
  simp

to_rcoset
@[simp] lemma lcoset_unit {α : Type} [Group α] {H : Subgroup α} :
  (1 : α) * H = (H : Set α) := by
  ext x
  simp

-- @[simp] lemma subgroup_of_subgroup {α : Type} [Group α]

lemma lcoset_eq_iff {α : Type} [Group α] {H : Subgroup α} {a b : α} :
  a * H = b * H ↔ a⁻¹ * b ∈ H := by
  constructor
  · intro h
    have : a ∈ a * H := self_in_lcoset
    rw [h] at this
    simp only [in_lcoset_iff] at this
    rcases this with ⟨h, ⟨h_h, h_bh⟩⟩
    have : a⁻¹ * b * h = h⁻¹ * h := by simp [h_bh]
    have : a⁻¹ * b = h⁻¹ := by simp [← right_cancel (a⁻¹ * b) h⁻¹ h, this]
    rw [this]
    simp [h_h]
  · intro h
    ext x
    have h_invb_a : b⁻¹ * a ∈ H := by
      rw [in_subgroup_iff_inv_in]
      rw [(by simp : (b⁻¹ * a)⁻¹ = a⁻¹ * b)]
      exact h
    constructor
    <;> intro hl
    <;> rw [in_lcoset_iff] at hl ⊢
    <;> rcases hl with ⟨h1, ⟨h_h1, h_ah1⟩⟩
    · use b⁻¹ * x
      constructor
      · rw [← h_ah1, ← mul_assoc]
        exact mul_mem h_invb_a h_h1
      · simp [← mul_assoc]
    · use a⁻¹ * x
      constructor
      · rw [← h_ah1, ← mul_assoc]
        exact mul_mem h h_h1
      · simp [← mul_assoc]

/-- Dual of `lcoset_eq_iff` (`to_rcoset` generates this statement automatically; the
proof is the hand-adjusted version of the transformed source proof). -/
lemma rcoset_eq_iff {α : Type} [Group α] {H : Subgroup α} {a b : α} :
  H * a = H * b ↔ b * a⁻¹ ∈ H := by
  constructor
  · intro h
    have : a ∈ H * a := self_in_rcoset
    rw [h] at this
    simp only [in_rcoset_iff] at this
    rcases this with ⟨k, ⟨k_h, h_kb⟩⟩
    have : b * a⁻¹ = k⁻¹ := by rw [← h_kb, inv_mul, ← mul_assoc]; simp
    rw [this]
    exact inv_mem k_h
  · intro h
    ext x
    have h_abinv : a * b⁻¹ ∈ H := by
      rw [in_subgroup_iff_inv_in]
      rw [(by simp : (a * b⁻¹)⁻¹ = b * a⁻¹)]
      exact h
    constructor
    <;> intro hl
    <;> rw [in_rcoset_iff] at hl ⊢
    <;> rcases hl with ⟨k, ⟨k_h, h_kx⟩⟩
    · use k * (a * b⁻¹)
      constructor
      · exact mul_mem k_h h_abinv
      · rw [← h_kx]; simp [mul_assoc]
    · use k * (b * a⁻¹)
      constructor
      · exact mul_mem k_h h
      · rw [← h_kx]; simp [mul_assoc]

@[simp] lemma lcoset_card {α : Type} [Group α] {H : Subgroup α} {a : α} :
  (a * H).encard = (H : Set α).encard := by
  rw [Set.encard_congr]
  let f : (a * H).Elem → (H : Set α).Elem :=
    fun x ↦ ⟨a⁻¹ * x, by aesop⟩
  have h_f : f.Bijective := by
    constructor
    · dsimp [Function.Injective]
      intro a1 a2
      aesop
    · dsimp [Function.Surjective]
      intro b
      use ⟨a * (b : α), by simp⟩
      simp only [f]
      have : a⁻¹ * (a * (b : α)) = b := by simp [← mul_assoc]
      simp [this]
  exact Equiv.ofBijective f h_f

@[simp] lemma rcoset_card {α : Type} [Group α] {H : Subgroup α} {a : α} :
  (H * a).encard = (H : Set α).encard := by
  rw [Set.encard_congr]
  let f : (H * a).Elem → (H : Set α).Elem :=
    fun x ↦ ⟨x * a⁻¹, by aesop⟩
  have h_f : f.Bijective := by
    constructor
    · dsimp [Function.Injective]
      intro a1 a2
      aesop
    · dsimp [Function.Surjective]
      intro b
      use ⟨(b : α) * a, by simp⟩
      simp only [f]
      simp
  exact Equiv.ofBijective f h_f

end Abstract
