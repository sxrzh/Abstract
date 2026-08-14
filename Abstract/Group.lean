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

@[simp] lemma pow_nat_zero {α : Type} [Group α] (a : α) : pow_nat a 0 = 1 := by rfl
@[simp] lemma pow_nat_one {α : Type} [Group α] (a : α) : pow_nat a 1 = a := by simp [pow_nat]
@[simp] lemma pow_nat_succ {α : Type} [Group α] (a : α) (n : ℕ) :
  pow_nat a (Nat.succ n) = pow_nat a n * a := by
  rw [pow_nat]
@[simp] lemma pow_nat_mul_self_comm {α : Type} [Group α] (a : α) (n : ℕ) :
  pow_nat a n * a = a * pow_nat a n := by
  induction n with
  | zero => simp
  | succ n h => simp [h]
@[simp] lemma pow_nat_mul_inv_comm {α : Type} [Group α] (a : α) (n : ℕ) :
  pow_nat a n * a⁻¹ = a⁻¹ * pow_nat a n := by
  induction n with
  | zero => simp
  | succ n h =>
      rw [pow_nat_succ]
      nth_rw 2 [pow_nat_mul_self_comm]
      rw [← mul_assoc, mul_assoc]
      simp
@[simp] lemma pow_nat_inv_mul_self_comm {α : Type} [Group α] (a : α) (n : ℕ) :
  pow_nat a⁻¹ n * a = a * pow_nat a⁻¹ n := by
  nth_rw 2 [← inv_inv a]
  nth_rw 3 [← inv_inv a]
  apply pow_nat_mul_inv_comm
@[simp] lemma pow_nat_succ_left {α : Type} [Group α] (a : α) (n : ℕ) :
  pow_nat a (Nat.succ n) = a * pow_nat a n := by
  rw [pow_nat_succ]
  apply pow_nat_mul_self_comm
@[simp] lemma pow_nat_add {α : Type} [Group α] (a : α) (n m : ℕ) :
  pow_nat a (n + m) = pow_nat a n * pow_nat a m := by
  induction m with
  | zero => simp
  | succ m h =>
      rw [Nat.add_succ]
      repeat rw [pow_nat_succ]
      simp [h]
@[simp] lemma inv_pow_nat {α : Type} [Group α] (a : α) (n : ℕ) :
  (pow_nat a n)⁻¹ = pow_nat (a⁻¹) n := by
  induction n with
  | zero => simp
  | succ n h => simp [h]
@[simp] lemma pow_nat_mul {α : Type} [Group α] (a : α) (n m : ℕ) :
  pow_nat a (n * m) = pow_nat (pow_nat a n) m := by
  induction m with
  | zero => simp
  | succ m h => simp [mul_add, h]

@[simp] lemma pow_int_zero {α : Type} [Group α] (a : α) : pow_int a 0 = 1 := by rfl
@[simp] lemma pow_int_one {α : Type} [Group α] (a : α) : pow_int a 1 = a := by simp [pow_int]
@[simp] lemma pow_int_neg_one {α : Type} [Group α] (a : α) : pow_int a (-1) = a⁻¹ := by
  change pow_int a (Int.negSucc 0) = a⁻¹
  simp [pow_int]
lemma pow_int_nonneg {α : Type} [Group α] {a : α} {n : ℤ} (h : n ≥ 0) :
  pow_int a n = pow_nat a n.toNat := by
  cases n with
  | ofNat n => simp [pow_int]
  | negSucc n =>
      have : Int.negSucc n < 0 := Int.negSucc_lt_zero n
      contradiction
@[simp] lemma pow_int_neg_nat {α : Type} [Group α] (a : α) (n : ℕ) :
  pow_int a (-n) = (pow_int a n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n h =>
      change pow_int a (Int.negSucc n) = (pow_int a (Int.ofNat (n + 1)))⁻¹
      simp [pow_int]
@[simp] lemma pow_int_neg {α : Type} [Group α] (a : α) (n : ℤ) :
  pow_int a (-n) = (pow_int a n)⁻¹ := by
  cases n with
  | ofNat n => apply pow_int_neg_nat
  | negSucc n =>
      have h_tonat : (-Int.negSucc n).toNat = n + 1 := by simp
      rw [pow_int, inv_inv]
      rw [pow_int_nonneg (by omega)]
      rw [h_tonat]

lemma pow_int_mul_self_comm {α : Type} [Group α] (a : α) (n : ℤ) :
  pow_int a n * a = a * pow_int a n := by
  cases n with
  | ofNat n => simp [pow_int]
  | negSucc n =>
      simp only [pow_int, pow_nat_succ, pow_nat_mul_self_comm, inv_mul, inv_pow_nat, mul_assoc,
        pow_nat_inv_mul_self_comm]
      rw [← mul_assoc]
      rw [← mul_assoc]
      simp
lemma pow_int_mul_inv_comm {α : Type} [Group α] (a : α) (n : ℤ) :
  pow_int a n * a⁻¹ = a⁻¹ * pow_int a n := by
  cases n with
  | ofNat n => simp [pow_int]
  | negSucc n => simp [pow_int]
lemma pow_int_inv_mul_self_comm {α : Type} [Group α] (a : α) (n : ℤ) :
  pow_int a⁻¹ n * a = a * pow_int a⁻¹ n := by
  nth_rw 2 [← inv_inv a]
  nth_rw 3 [← inv_inv a]
  apply pow_int_mul_inv_comm

lemma pow_int_succ {α : Type} [Group α] (a : α) (n : ℤ) :
  pow_int a (Int.succ n) = pow_int a n * a := by
  cases n with
  | ofNat n =>
      simp only [Int.ofNat_eq_natCast]
      apply pow_nat_succ
  | negSucc t =>
      have : (Int.negSucc t).succ = -t := by simp [Int.succ]
      rw [this]
      cases t with
      | zero => simp
      | succ t =>
          change pow_int a (Int.negSucc t) = pow_int a (Int.negSucc (t + 1)) * a
          symm
          simp only [pow_int, pow_nat_succ, mul_assoc, inv_mul, inv_pow_nat, left_cancel]
          calc a⁻¹ * (pow_nat a⁻¹ t * a)
            = a⁻¹ * (a * pow_nat a⁻¹ t) := by simp
          _ = a⁻¹ * a * pow_nat a⁻¹ t := by rw [mul_assoc]
          _ = pow_nat a⁻¹ t := by simp

@[simp] lemma pow_int_add_one {α : Type} [Group α] (a : α) (n : ℤ) :
  pow_int a (n + 1) = pow_int a n * a := by
  apply pow_int_succ

@[simp] lemma pow_int_pred {α : Type} [Group α] (a : α) (n : ℤ) :
  pow_int a (Int.pred n) = pow_int a n * a⁻¹ := by
  let m := Int.pred n
  have : n = Int.succ m := by rw [Int.succ_pred]
  change pow_int a m = pow_int a n * a⁻¹
  rw [this]
  symm
  calc pow_int a m.succ * a⁻¹
  _ = pow_int a m * a * a⁻¹ := by rw [pow_int_succ]
  _ = pow_int a m := by simp

@[simp] lemma pow_int_sub_one {α : Type} [Group α] (a : α) (n : ℤ) :
  pow_int a (n - 1) = pow_int a n * a⁻¹ := by
  apply pow_int_pred

@[simp] lemma inv_pow_int {α : Type} [Group α] (a : α) (n : ℤ) :
  (pow_int a n)⁻¹ = pow_int a⁻¹ n := by
  induction n with
  | zero => simp
  | succ n h => simp [h, pow_int_mul_self_comm]
  | pred n h =>
      simp at h
      simp [← h]
      simp [pow_int_mul_self_comm]

@[simp] lemma pow_int_nonpos {α : Type} [Group α] {a : α} {n : ℤ} (h : n ≤ 0) :
  pow_int a n = (pow_nat a (-n).toNat)⁻¹ := by
  have : -n ≥ 0 := by omega
  rw [← pow_int_nonneg this]
  simp

@[simp] lemma pow_int_add {α : Type} [Group α] (a : α) (n m : ℤ) :
  pow_int a (n + m) = pow_int a n * pow_int a m := by
  induction m with
  | zero => simp
  | succ m h =>
      calc pow_int a (n + (m + 1))
        = pow_int a (n + m + 1) := by rw [add_assoc]
      _ = pow_int a (n + m) * a := by apply pow_int_succ
      _ = pow_int a n * pow_int a m * a := by rw [h]
      _ = pow_int a n * (pow_int a m * a) := by simp
      _ = pow_int a n * pow_int a (m + 1) := by rw [← pow_int_succ, Int.succ]
  | pred m h =>
      calc pow_int a (n + (- m - 1))
        = pow_int a (n + - m - 1) := by rw [add_sub, ← sub_eq_add_neg]
      _ = pow_int a (n + - m).pred := by norm_cast
      _ = pow_int a n * pow_int a (- m) * a⁻¹ := by simp [h]
      _ = pow_int a n * pow_int a (- m : ℤ).pred := by simp
      _ = pow_int a n * pow_int a (- m - 1) := by norm_cast

@[simp] lemma pow_int_sub {α : Type} [Group α] (a : α) (n m : ℤ) :
  pow_int a (n - m) = pow_int a n * (pow_int a m)⁻¹ := by
  change pow_int a (n + - m) = pow_int a n * (pow_int a m)⁻¹
  simp

@[simp] lemma pow_int_mul {α : Type} [Group α] (a : α) (n m : ℤ) :
  pow_int a (n * m) = pow_int (pow_int a n) m := by
  by_cases h_n : n ≥ 0
  · by_cases h_m : m ≥ 0
    · have : n * m ≥ 0 := Int.mul_nonneg h_n h_m
      rw [pow_int_nonneg h_n, pow_int_nonneg h_m, pow_int_nonneg this]
      rw [Int.toNat_mul h_n h_m]
      apply pow_nat_mul
    · have h_m' : m ≤ 0 := by omega
      have : n * m ≤ 0 := by nlinarith
      rw [pow_int_nonpos this]
      have : -(n * m) = n * (-m) := by norm_num
      rw [this]
      rw [Int.toNat_mul (by omega) (by omega)]
      simp [pow_int_nonneg h_n, pow_int_nonpos h_m']
  · by_cases h_m : m ≥ 0
    · have h_n' : n ≤ 0 := by omega
      have : n * m ≤ 0 := by nlinarith
      rw [pow_int_nonpos this]
      have : -(n * m) = (-n) * m := by norm_num
      rw [this]
      rw [Int.toNat_mul (by omega) (by omega)]
      simp [pow_int_nonpos h_n', pow_int_nonneg h_m]
    · have h_n' : n ≤ 0 := by omega
      have h_m' : m ≤ 0 := by omega
      have : n * m = -n * -m := by norm_num
      rw [this]
      have : (-n) * (-m) ≥ 0 := by nlinarith
      rw [pow_int_nonneg this]
      rw [Int.toNat_mul (by omega) (by omega)]
      simp [pow_int_nonpos h_n',
        pow_int_nonpos h_m']

@[simp] lemma pow_zero {α : Type} [Group α] (a : α) : a ^ (0 : ℤ) = 1 := rfl
@[simp] lemma pow_one {α : Type} [Group α] (a : α) : a ^ (1 : ℤ) = a := by
  apply pow_int_one
@[simp] lemma pow_neg_one {α : Type} [Group α] (a : α) : a ^ (-1 : ℤ) = a⁻¹ := by
  apply pow_int_neg_one
@[simp] lemma pow_neg {α : Type} [Group α] (a : α) (n : ℤ) : a ^ (- n) = (a ^ n)⁻¹ := by
  apply pow_int_neg
@[simp] lemma pow_inv {α : Type} [Group α] (a : α) (n : ℤ) : (a ^ n)⁻¹ = a⁻¹ ^ n := by
  apply inv_pow_int
@[simp] lemma pow_add {α : Type} [Group α] (a : α) (n m : ℤ) : a ^ (n + m) = a ^ n * a ^ m := by
  apply pow_int_add
@[simp] lemma pow_sub {α : Type} [Group α] (a : α) (n m : ℤ) : a ^ (n - m) = a ^ n * (a ^ m)⁻¹ := by
  apply pow_int_sub
@[simp] lemma pow_mul {α : Type} [Group α] (a : α) (n m : ℤ) : a ^ (n * m) = (a ^ n) ^ m := by
  apply pow_int_mul

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
