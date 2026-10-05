import Croot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Harmonic sums over intervals

`∑_{n=N+1}^{M} 1/n` lies between `log((M+1)/(N+1))` and `log(M/N)`, and the
"harmonic block" `(N, M]` with `1 ≤ ∑ < 1 + 1/M` has `e N ≤ M ≤ e N + 3`.
-/

namespace Croot

open Real Finset

/-- Peeling off the top point of `(N, M + 1]`. -/
lemma recipSum_Ioc_succ {N M : ℕ} (h : N ≤ M) :
    recipSum (Ioc N (M + 1)) = recipSum (Ioc N M) + 1 / ((M : ℚ) + 1) := by
  rw [recipSum, Finset.sum_Ioc_succ_top h, recipSum]
  push_cast
  ring

/-- `(N, M]` is empty when `M ≤ N`. -/
lemma recipSum_Ioc_of_le {N M : ℕ} (h : M ≤ N) : recipSum (Ioc N M) = 0 := by
  rw [Finset.Ioc_eq_empty_of_le h, recipSum_empty]

/-- `1/(x+1) ≤ log (x+1) - log x` for `x > 0` (from `log t ≤ t - 1` at `t = x/(x+1)`). -/
lemma one_div_add_one_le_log_sub {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / (x + 1) by positivity)
  rw [Real.log_div hx.ne' (by positivity)] at h
  have e : x / (x + 1) - 1 = -(1 / (x + 1)) := by field_simp; ring
  linarith

/-- `log (x+1) - log x ≤ 1/x` for `x > 0` (from `log t ≤ t - 1` at `t = (x+1)/x`). -/
lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) hx.ne'] at h
  have e : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

/-- `∑_{n=N+1}^{M} 1/n ≤ log (M/N)`. -/
theorem recipSum_Ioc_le_log {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    ((recipSum (Ioc N M) : ℚ) : ℝ) ≤ Real.log ((M : ℝ) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  induction M, hNM using Nat.le_induction with
  | base =>
    rw [recipSum_Ioc_of_le le_rfl, div_self hN0.ne', Real.log_one, Rat.cast_zero]
  | succ M hNM ih =>
    have hM0 : (0 : ℝ) < M := by
      have : (1 : ℝ) ≤ M := by exact_mod_cast hN.trans hNM
      linarith
    have key := one_div_add_one_le_log_sub hM0
    rw [Real.log_div hM0.ne' hN0.ne'] at ih
    rw [recipSum_Ioc_succ hNM, Rat.cast_add, Real.log_div (by positivity) hN0.ne']
    push_cast
    linarith

/-- `log ((M+1)/(N+1)) ≤ ∑_{n=N+1}^{M} 1/n`. -/
theorem log_le_recipSum_Ioc {N M : ℕ} (hNM : N ≤ M) :
    Real.log (((M : ℝ) + 1) / ((N : ℝ) + 1)) ≤ ((recipSum (Ioc N M) : ℚ) : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  induction M, hNM using Nat.le_induction with
  | base =>
    rw [recipSum_Ioc_of_le le_rfl, div_self hN0.ne', Real.log_one, Rat.cast_zero]
  | succ M hNM ih =>
    have hM0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have key := log_add_one_sub_log_le hM0
    rw [Real.log_div hM0.ne' hN0.ne'] at ih
    rw [recipSum_Ioc_succ hNM, Rat.cast_add]
    push_cast
    rw [Real.log_div (by positivity) hN0.ne']
    linarith

/-- The harmonic block starting after `N`. -/
theorem exists_harmonic_block {N : ℕ} (hN : 1 ≤ N) : ∃ M : ℕ, N < M ∧
    1 ≤ recipSum (Ioc N M) ∧ recipSum (Ioc N M) < 1 + 1 / (M : ℚ) ∧
    Real.exp 1 * N ≤ M ∧ (M : ℝ) ≤ Real.exp 1 * N + 3 := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  -- some `m` has `H((N, m]) ≥ 1`: take `m = 3N + 3`, so `(m+1)/(N+1) ≥ 3 > e`
  have hex : ∃ m : ℕ, 1 ≤ recipSum (Ioc N m) := by
    refine ⟨3 * N + 3, ?_⟩
    have h := log_le_recipSum_Ioc (N := N) (M := 3 * N + 3) (by omega)
    have h1 : (1 : ℝ) ≤ Real.log ((((3 * N + 3 : ℕ) : ℝ) + 1) / ((N : ℝ) + 1)) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
      push_cast
      nlinarith
    have h2 : ((1 : ℚ) : ℝ) ≤ ((recipSum (Ioc N (3 * N + 3)) : ℚ) : ℝ) := by
      rw [Rat.cast_one]; exact h1.trans h
    exact_mod_cast h2
  -- `M` is the least such `m`
  obtain ⟨M, hM1, hmin⟩ : ∃ M, 1 ≤ recipSum (Ioc N M) ∧
      ∀ m < M, ¬ 1 ≤ recipSum (Ioc N m) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hNM : N < M := by
    by_contra h
    rw [recipSum_Ioc_of_le (not_lt.1 h)] at hM1
    norm_num at hM1
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hNM' : N ≤ M' := by omega
  have hlt : recipSum (Ioc N M') < 1 := lt_of_not_ge (hmin M' (by omega))
  have hsucc := recipSum_Ioc_succ hNM'
  refine ⟨M' + 1, hNM, hM1, ?_, ?_, ?_⟩
  · -- minimality: `H((N, M]) = H((N, M - 1]) + 1/M < 1 + 1/M`
    rw [hsucc]
    push_cast
    linarith
  · -- upper bound: `1 ≤ H((N, M]) ≤ log (M / N)`, so `e ≤ M / N`
    have h := recipSum_Ioc_le_log hN hNM.le
    have h1 : ((1 : ℚ) : ℝ) ≤ ((recipSum (Ioc N (M' + 1)) : ℚ) : ℝ) := by exact_mod_cast hM1
    rw [Rat.cast_one] at h1
    have h2 : (1 : ℝ) ≤ Real.log (((M' + 1 : ℕ) : ℝ) / N) := h1.trans h
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hN0] at h2
    exact h2
  · -- lower bound at `M - 1`: `log (M/(N+1)) ≤ H((N, M - 1]) < 1`, so `M < e (N + 1)`
    have h := log_le_recipSum_Ioc hNM'
    have h1 : ((recipSum (Ioc N M') : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := by exact_mod_cast hlt
    rw [Rat.cast_one] at h1
    have h2 : Real.log (((M' : ℝ) + 1) / ((N : ℝ) + 1)) < 1 := h.trans_lt h1
    rw [Real.log_lt_iff_lt_exp (by positivity), div_lt_iff₀ (by positivity)] at h2
    push_cast
    nlinarith

end Croot
