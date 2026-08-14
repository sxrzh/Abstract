
          -- change pow_int a (-(n+1)+1) = pow_int a (-(n+1)) * a
        -- change pow_int a (-(n + 1) + 1) = pow_int a (Int.negSucc n) * a
        -- have (n : ℕ): -((n : ℤ) + 1) + 1 = -(n : ℤ) := by
        --   simp
        -- simp [this (n + 1)]




      -- rw [this, pow_int_neg]
      -- simp [pow_int]
      -- induction n with
      -- | zero =>
      --     have : (-1).succ = 0 := by decide
      --     simp [this]
      -- | succ n h => sorry


-- calc pow_int a (Int.negSucc (n + 1)).succ
--             = pow_int a ((Int.negSucc n) - 1).succ := by simp
--           _ = pow_int a (Int.negSucc n) := by
--                   change pow_int a (Int.pred (Int.negSucc n)).succ = pow_int a (Int.negSucc n)
--                   rw [Int.succ_pred]
--           _ = pow_int a (Int.negSucc n) * a * a⁻¹ := by simp
--           _ = pow_int a (Int.negSucc n).succ * a⁻¹ := by rw [h]
--           _ = pow_int a (Int.negSucc (n + 1)) * a
