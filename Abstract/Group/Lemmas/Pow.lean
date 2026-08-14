import Mathlib
import Abstract.Group.Defs
import Abstract.Group.Lemmas.MulInv

namespace Abstract

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

end Abstract
