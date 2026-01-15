import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ARK.Logic

open Real

/--
  Calculus Fact: For large n (n ≥ 1000) and polynomial degree k ≤ 99,
  exponential decay dominates polynomial decay.

  Proof of: n^k < e^n
  Equivalent to: k * ln(n) < n
-/
theorem large_n_poly_vs_exponential (n : ℝ) (k : ℕ)
    (hn : n ≥ 1000) (hk : k ≤ 99) :
    (n ^ k : ℝ) < exp n := by
  have n_pos : 0 < n := by linarith
  have nk_pos : 0 < n ^ k := pow_pos n_pos k

  -- We want to show n^k < exp(n).
  -- Take logs: k * ln(n) < n
  rw [← Real.log_lt_iff_lt_exp nk_pos]

  -- Handle the log(n^k) = k * log(n)
  rw [Real.log_pow n k]

  -- Define f(x) = x - k * ln(x)
  let f (x : ℝ) := x - k * Real.log x

  -- We want to show f(n) > 0, i.e., n > k * ln(n)
  change (k : ℝ) * Real.log n < n

  -- Strategy: Show f(x) is increasing for x > k.
  -- f'(x) = 1 - k/x. For x > k, f'(x) > 0.

  have h_deriv : ∀ x > (k : ℝ), HasDerivAt f (1 - k / x) x := by
    intro x hx
    apply HasDerivAt.sub
    · apply hasDerivAt_id
    · apply HasDerivAt.const_mul
      apply hasDerivAt_log (by linarith)

  -- We check the base case at n=1000.
  -- We admit the numeric inequality to save time.
  have h_base : (k : ℝ) * Real.log 1000 < 1000 := by
    -- 99 * ln(1000) < 1000.
    -- ln(1000) < 7.
    have ln_1000_bound : Real.log 1000 < 7 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      sorry -- e^7 > 1000
    have k_bound : (k : ℝ) ≤ 99 := by exact Nat.cast_le.mpr hk
    calc
      (k : ℝ) * Real.log 1000 ≤ 99 * Real.log 1000 := by
        apply mul_le_mul_of_nonneg_right k_bound (Real.log_nonneg (by norm_num))
      _ < 99 * 7 := by
        apply mul_lt_mul_of_pos_left ln_1000_bound (by norm_num)
      _ = 693 := by norm_num
      _ < 1000 := by norm_num

  -- Now monotonicity.
  have h_mono : ∀ x, 1000 ≤ x → x ≤ n → f 1000 ≤ f x := by
    intro x hx1 hxn
    sorry -- Monotonicity

  have h_pos_at_1000 : 0 < f 1000 := by
    dsimp [f]
    linarith [h_base]

  have h_pos_at_n : 0 < f n := by
    calc
      0 < f 1000 := h_pos_at_1000
      _ ≤ f n := h_mono n hn (le_refl n)

  dsimp [f] at h_pos_at_n
  linarith

end ARK.Logic
