import Mathlib

namespace Abstract

class Semigroup (α : Type) where
  mul : α → α → α
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)

infixl:70 " * " => Semigroup.mul

class Monoid (α : Type) extends Semigroup α where
  unit : α
  unit_def : ∀ a, unit * a = a ∧ a * unit = a

instance {α : Type} [Monoid α] : One α where
  one := Monoid.unit

class Group (α : Type) extends Monoid α where
  inv : α → α
  inv_def : ∀ a, (inv a) * a = unit ∧ a * (inv a) = unit

instance {α : Type} [Group α] : Inv α where
  inv := Group.inv

-- infixl:70 " ^ " => pow_int

class AbelianGroup (α : Type) extends Group α where
  mul_comm : ∀ x y, mul x y = mul y x

attribute [simp] Semigroup.mul_assoc
attribute [simp] AbelianGroup.mul_comm

export Semigroup (mul_assoc)
export Monoid (unit_def)
export Group (inv_def)
export AbelianGroup (mul_comm)

example : Semigroup ℕ where
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc

example : Group ℤ where
  mul := Int.add
  mul_assoc := Int.add_assoc
  unit := 0
  unit_def := by simp
  inv := Int.neg
  inv_def := by
    intro a
    constructor
    · apply Int.add_left_neg
    · apply Int.add_right_neg

example : Monoid ℤ where
  mul := Int.mul
  mul_assoc := Int.mul_assoc
  unit := 1
  unit_def := by simp

example : Group ℚ where
  mul := Rat.add
  mul_assoc := Rat.add_assoc
  unit := 0
  unit_def := by
    intro a
    constructor
    · apply Rat.zero_add
    · apply Rat.add_zero
  inv := Rat.neg
  inv_def := by
    intro a
    constructor
    · apply Rat.neg_add_cancel
    · apply Rat.add_neg_cancel

def pow_nat {α : Type} [Monoid α] (a : α) : ℕ → α
  | 0 => 1
  | Nat.succ n => pow_nat a n * a

def pow_int {α : Type} [Group α] (a : α) : ℤ → α
  | Int.ofNat n => pow_nat a n
  | Int.negSucc n => (pow_nat a (n + 1))⁻¹

instance {G : Type} [Group G] : Pow G ℤ where
  pow := pow_int

instance {G : Type} [Group G] : Pow G ℕ where
  pow := pow_nat

end Abstract
