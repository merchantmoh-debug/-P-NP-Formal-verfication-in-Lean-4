import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

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

  -- Case k = 0
  by_cases hk0 : k = 0
  · rw [hk0, pow_zero]
    exact one_lt_exp (lt_of_lt_of_le (by norm_num) hn)
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0

  -- Equivalence: n^k < e^n <-> k log n < n
  rw [← log_lt_iff_lt_exp (pow_pos (lt_of_lt_of_le (by norm_num) hn) _)]
  rw [log_pow]
  simp only [natCast_zpow, id_eq]

  -- Function g(x) = x - k log x
  let g := fun (x : ℝ) => x - (k : ℝ) * log x

  -- We want g(n) > 0.
  -- 1. Bound log 1000 < 10
  have h_log_bound : log 1000 < 10 := by
    rw [← lt_exp_iff_log_lt (by norm_num)]
    calc
      (1000 : ℝ) < 1024 := by norm_num
      _ = 2 ^ 10 := by norm_num
      _ < (exp 1) ^ 10 := pow_lt_pow_left_of_lt_left (Real.two_lt_exp_one) (by norm_num) (by norm_num)
      _ = exp 10 := by rw [exp_nat_hom, Real.exp_one_rpow]

  -- 2. Check g(1000) > 0
  have g_1000_pos : g 1000 > 0 := by
    dsimp [g]
    rw [sub_pos]
    calc
      (k : ℝ) * log 1000 ≤ 99 * log 1000 := mul_le_mul_of_nonneg_right (by norm_cast) (log_nonneg (by norm_num))
      _ < 99 * 10 := mul_lt_mul_of_pos_left h_log_bound (by norm_num)
      _ = 990 := by norm_num
      _ < 1000 := by norm_num

  -- 3. Monotonicity: g is strictly increasing on [1000, ∞)
  -- deriv g(x) = 1 - k/x
  have g_mono : StrictMonoOn g (Set.Ici 1000) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1000)
    · -- Continuous / Differentiable
      intro x hx
      apply DifferentiableAt.sub (differentiableAt_id)
      apply DifferentiableAt.mul (differentiableAt_const _)
      apply differentiableAt_log
      linarith
    · -- Derivative positive
      intro x hx inner
      rw [deriv_sub, deriv_id, deriv_const_mul, deriv_log]
      · simp only [one_div, mul_one]
        rw [sub_pos, div_lt_iff]
        · calc
            (k : ℝ) ≤ 99 := by norm_cast
            _ < 1000 := by norm_num
            _ ≤ x := hx
        · linarith
      · exact differentiableAt_id
      · apply differentiableAt_const_mul
        apply differentiableAt_log
        linarith
      · apply DifferentiableAt.sub differentiableAt_id
        apply DifferentiableAt.mul (differentiableAt_const _)
        apply differentiableAt_log
        linarith

  -- 4. Conclusion
  -- If n = 1000, g(n) > 0. If n > 1000, g(n) > g(1000) > 0.
  cases le_iff_eq_or_lt.mp hn with
  | inl h_eq =>
      rw [← h_eq] at g_1000_pos
      simp [g] at g_1000_pos
      exact g_1000_pos
  | inr h_lt =>
      have : g 1000 < g n := g_mono (le_refl 1000) hn h_lt
      simp [g] at g_1000_pos
      simp [g] at this
      linarith

end ARK.Logic
