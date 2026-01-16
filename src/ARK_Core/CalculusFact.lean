import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum

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
  have log_n_pos : 0 < log n := log_pos (by linarith)

  -- Transform n^k < exp n  <->  log(n^k) < log(exp n)  <->  k * log n < n
  rw [← log_lt_log_iff (pow_pos n_pos k) (exp_pos _), log_exp, log_pow n k]

  -- We suffice to show 99 * log n < n
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (le_of_lt log_n_pos))

  -- Let f(x) = x - 99 * log x. We show f(x) > 0 for x >= 1000.
  let f := fun x => x - 99 * log x

  -- First, show f is monotone increasing on [1000, ∞)
  have h_mono : MonotoneOn f (Set.Ici 1000) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1000)
    · -- ContinuousOn
      apply ContinuousOn.sub continuousOn_id
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log continuousOn_id
      intro x hx
      simp only [Set.mem_Ici] at hx
      dsimp
      linarith
    · -- Derivative in interior (1000, ∞)
      intro x hx
      -- interior (Ici 1000) is Ioi 1000
      have x_pos : x ≠ 0 := by rw [interior_Ici, Set.mem_Ioi] at hx; linarith
      apply HasDerivAt.hasDerivWithinAt
      apply HasDerivAt.sub
      · apply hasDerivAt_id
      · apply HasDerivAt.const_mul
        apply hasDerivAt_log x_pos
    · -- Derivative non-negative
      intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      dsimp
      -- 1 - 99/x >= 0
      change 0 ≤ 1 - 99 / x
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith

  -- Now show f(1000) > 0
  have h_base : 0 < f 1000 := by
    simp only [f]
    rw [sub_pos]

    -- Prove log 1000 < 7
    have h_log_bound : log 1000 < 7 := by
      rw [log_lt_iff_lt_exp (by norm_num : 0 < (1000:ℝ))]
      -- 2.718 < e
      have h_base_e : (2718/1000 : ℝ) < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
      -- (2.718)^7 < e^7
      have h_pow : (2718/1000 : ℝ) ^ 7 < exp 7 := by
         conv_rhs => rw [(by norm_num : (7:ℝ) = ↑(7:ℕ) * 1), Real.exp_nat_mul]
         refine pow_lt_pow_left₀ (n := 7) h_base_e ?_ ?_
         · norm_num
         · norm_num

      -- 1000 < (2.718)^7
      -- (2718/1000)^7 = 2718^7 / 1000^7
      have h_calc : (1000 : ℝ) < (2718/1000) ^ 7 := by
        rw [div_pow]
        rw [lt_div_iff₀ (by norm_num : 0 < (1000^7 : ℝ))]
        norm_num

      linarith

    apply lt_of_lt_of_le (b := 99 * 7)
    · apply mul_lt_mul_of_pos_left h_log_bound (by norm_num)
    · norm_num -- 693 < 1000

  -- Conclusion
  have h_res : 0 < f n := by
    apply lt_of_lt_of_le h_base
    apply h_mono (Set.mem_Ici.mpr (le_refl 1000)) hn hn

  simp only [f, sub_pos] at h_res
  exact h_res

end ARK.Logic
