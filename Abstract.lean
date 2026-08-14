import Abstract.Basic

import Init.Data.Int.Basic -- 或直接 import Init

example (n : Nat) : (Int.negSucc n).succ = -n := rfl
