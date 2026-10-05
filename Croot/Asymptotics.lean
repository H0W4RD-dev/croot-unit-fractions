import Croot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Elementary asymptotic facts used in the assembly of Croot's theorem

All statements are of the form "for all sufficiently large `M` (or `N`)"; they only involve
powers, logarithms, `exp`, `Nat.log`, floors and `Nat.lcmUpto` (bounded via Chebyshev's
elementary estimates `2 ^ n ≤ (n + 1) lcm(1..n)` and `ψ(n) ≤ π(n) log n`).
-/

namespace Croot

open Real Finset Filter

namespace AsymAux

/-! ### Generic eventual bounds along `ℕ` -/

lemma ev_rpow_ge {s : ℝ} (hs : 0 < s) (C : ℝ) : ∀ᶠ M : ℕ in atTop, C ≤ (M : ℝ) ^ s :=
  tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hs).eventually_ge_atTop C)

lemma ev_log_ge (C : ℝ) : ∀ᶠ M : ℕ in atTop, C ≤ Real.log (M : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop C)

/-- `(log M)^n ≤ c M^s` eventually, for any `s > 0` and `c > 0`. -/
lemma ev_log_pow_le (n : ℕ) {s : ℝ} (hs : 0 < s) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ M : ℕ in atTop, Real.log (M : ℝ) ^ n ≤ c * (M : ℝ) ^ s := by
  have h : ∀ᶠ x : ℝ in atTop, Real.log x ^ n ≤ c * x ^ s := by
    filter_upwards [(isLittleO_log_rpow_rpow_atTop (n : ℝ) hs).bound hc,
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h1 : ‖Real.log x ^ (n : ℝ)‖ = Real.log x ^ n := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _), Real.rpow_natCast]
    have h2 : ‖x ^ s‖ = x ^ s := Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)
    calc Real.log x ^ n = ‖Real.log x ^ (n : ℝ)‖ := h1.symm
      _ ≤ c * ‖x ^ s‖ := hx
      _ = c * x ^ s := by rw [h2]
  exact tendsto_natCast_atTop_atTop.eventually h

/-! ### Numerical facts about logarithms -/

lemma log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  have h2 : (1 : ℝ) - 2⁻¹ = 1 / 2 := by norm_num
  linarith

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

lemma log_four_le_three : Real.log 4 ≤ 3 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  linarith

/-! ### The individual clauses of `prop2_eventually`, for a real variable `x` -/

lemma clause2 {x : ℝ} (hx : 0 < x) (hL : 2 ≤ Real.log x) :
    2 * x ^ (3 / 4 : ℝ) < x ^ (3 / 4 : ℝ) * Real.log x ^ 4 := by
  have h1 : 0 < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  have h2 : (2 : ℝ) ^ 4 ≤ Real.log x ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  nlinarith [mul_le_mul_of_nonneg_left h2 h1.le]

lemma clause3 {x : ℝ} (hx : 0 < x) (h4 : 3 ≤ x ^ (1 / 4 : ℝ)) :
    x ^ (3 / 4 : ℝ) < x / 2 := by
  have e : x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x := by
    rw [← Real.rpow_add hx]; norm_num
  have h1 : 0 < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  nlinarith [mul_le_mul_of_nonneg_left h4 h1.le]

/-- Clause 4: written with `w = x^{1/420}`, it reduces to `12 (log x)^4 ≤ w`. -/
lemma clause4 {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y) (hy : y ≤ x ^ (1 / 5 : ℝ))
    (hL : 1 ≤ Real.log x) (hw1 : 1 ≤ x ^ (1 / 420 : ℝ))
    (hkey : Real.log x ^ 4 ≤ 1 / 12 * x ^ (1 / 420 : ℝ)) :
    (2 * (x ^ (3 / 4 : ℝ) * Real.log x ^ 4) + 1) * (y + 1) / x ≤ x ^ (-(1 / 21 : ℝ)) / 2 := by
  have e1 : x ^ (3 / 4 : ℝ) = (x ^ (1 / 420 : ℝ)) ^ (315 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have e2 : x ^ (1 / 5 : ℝ) = (x ^ (1 / 420 : ℝ)) ^ (84 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have e5 : x ^ (-(1 / 21 : ℝ)) / 2 * x = (x ^ (1 / 420 : ℝ)) ^ (400 : ℕ) / 2 := by
    rw [div_mul_eq_mul_div, ← Real.rpow_add_one hx.ne', ← Real.rpow_natCast,
      ← Real.rpow_mul hx.le]
    norm_num
  rw [div_le_iff₀ hx, e5, e1]
  rw [e2] at hy
  generalize Real.log x = L at hL hkey ⊢
  generalize x ^ (1 / 420 : ℝ) = w at hw1 hkey hy ⊢
  have hA : 1 ≤ w ^ 315 * L ^ 4 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hw1) (one_le_pow₀ hL)
  have hC : 1 ≤ w ^ 84 := one_le_pow₀ hw1
  have hw0 : 0 ≤ w := by linarith
  calc (2 * (w ^ 315 * L ^ 4) + 1) * (y + 1)
      ≤ (3 * (w ^ 315 * L ^ 4)) * (2 * w ^ 84) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    _ = w ^ 399 * (6 * L ^ 4) := by ring
    _ ≤ w ^ 399 * (w / 2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = w ^ 400 / 2 := by ring

lemma clause5 {x η : ℝ} (hx : 0 < x) (hη : 0 < η) (h3 : x ^ (3 / 4 : ℝ) < x / 2) :
    x ^ (3 / 4 : ℝ) / ((1 + η) * x) ≤ 1 / 2 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hη hx]

/-- Clause 6, via Chebyshev's lower bound `ψ(u) ≥ (u - 1) log 2 - log (u + 2)`. -/
lemma clause6 {x : ℝ} (hx : 0 < x) (hu : 12 ≤ x ^ (1 / 5 : ℝ))
    (hlog : Real.log x ≤ 1 / 4 * x ^ (1 / 5 : ℝ)) :
    2 * x ^ (3 / 4 : ℝ) < (Nat.lcmUpto ⌊x ^ (1 / 5 : ℝ)⌋₊ : ℝ) := by
  have hu0 : 0 < x ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hx _
  have hP : (0 : ℝ) < (Nat.lcmUpto ⌊x ^ (1 / 5 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos _
  have hpsi : (x ^ (1 / 5 : ℝ) - 1) * Real.log 2 - Real.log (x ^ (1 / 5 : ℝ) + 2) ≤
      Real.log (Nat.lcmUpto ⌊x ^ (1 / 5 : ℝ)⌋₊ : ℝ) := by
    rw [← Chebyshev.psi_eq_log_lcmUpto, ← Chebyshev.psi_eq_psi_coe_floor]
    exact Chebyshev.psi_ge' hu0.le
  have hlog2 := log_two_ge_half
  have hlog2' := log_two_le_one
  have hlu : Real.log (x ^ (1 / 5 : ℝ)) = 1 / 5 * Real.log x := Real.log_rpow hx _
  have hmul : Real.log (2 * x ^ (1 / 5 : ℝ)) = Real.log 2 + Real.log (x ^ (1 / 5 : ℝ)) :=
    Real.log_mul two_ne_zero hu0.ne'
  have hlu2 : Real.log (x ^ (1 / 5 : ℝ) + 2) ≤ Real.log (2 * x ^ (1 / 5 : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have ha0 : 0 < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx _
  have hlhs : Real.log (2 * x ^ (3 / 4 : ℝ)) = Real.log 2 + 3 / 4 * Real.log x := by
    rw [Real.log_mul two_ne_zero ha0.ne', Real.log_rpow hx]
  rw [← Real.log_lt_log_iff (by positivity) hP, hlhs]
  have hprod : 0 ≤ (x ^ (1 / 5 : ℝ) - 1) * (Real.log 2 - 1 / 2) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- The algebraic core of clause 7 (with `r = x^{1/20}`). -/
lemma clause7_core {x L D η cG B : ℝ} (hx : 0 < x) (hη : 0 < η) (hη1 : η ≤ 1) (hcG : 0 < cG)
    (hB : 0 < B) (hL : 1 ≤ L) (hD0 : 0 < D) (hD : D ≤ 27 * L ^ 3 * B)
    (hr : 216 * B / cG ≤ x ^ (1 / 20 : ℝ)) :
    8 * x ^ (1 / 5 : ℝ) ≤
      4 * (x ^ (3 / 4 : ℝ) / ((1 + η) * x)) ^ 2 * (cG * (x ^ (3 / 4 : ℝ) * L ^ 4)) / D := by
  have e_a : x ^ (3 / 4 : ℝ) = (x ^ (1 / 20 : ℝ)) ^ (15 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have e_u : x ^ (1 / 5 : ℝ) = (x ^ (1 / 20 : ℝ)) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have e_x : x = (x ^ (1 / 20 : ℝ)) ^ (20 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have hr0 : 0 < x ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hx _
  rw [e_a, e_u]
  generalize x ^ (1 / 20 : ℝ) = r at e_x hr hr0 ⊢
  subst e_x
  rw [div_le_iff₀ hcG] at hr
  have key : 4 * (r ^ 15 / ((1 + η) * (r ^ 20))) ^ 2 * (cG * (r ^ 15 * L ^ 4)) / D
      = 4 * cG * r ^ 5 * L ^ 4 / ((1 + η) ^ 2 * D) := by
    have hr' : r ≠ 0 := hr0.ne'
    have hη' : 1 + η ≠ 0 := by positivity
    have hD' : D ≠ 0 := hD0.ne'
    field_simp
  rw [key, le_div_iff₀ (by positivity)]
  have h1 : (1 + η) ^ 2 ≤ 4 := by nlinarith
  have h2 : (1 + η) ^ 2 * D ≤ 4 * (27 * L ^ 3 * B) := mul_le_mul h1 hD hD0.le (by norm_num)
  have h3 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
  calc 8 * r ^ 4 * ((1 + η) ^ 2 * D) ≤ 8 * r ^ 4 * (4 * (27 * L ^ 3 * B)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 4 * (216 * B) * r ^ 4 * L ^ 3 := by ring
    _ ≤ 4 * (216 * B) * r ^ 4 * L ^ 4 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ 4 * (r * cG) * r ^ 4 * L ^ 4 := by gcongr
    _ = 4 * cG * r ^ 5 * L ^ 4 := by ring

/-- Clause 7: `log (2 P) ≤ log 2 + ψ(M^{1/5}) ≤ 8 M^{1/5}`, while the exponent is
`≥ cG M^{1/4} (log M)^4 / D` with `D ≤ 27 (log M)^3 B`. -/
lemma clause7 {η cG : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hcG : 0 < cG) {B : ℕ} (hB : 0 < B)
    {M : ℕ} (hM : 0 < M) (hL : 4 ≤ Real.log M) (hr : 216 * B / cG ≤ (M : ℝ) ^ (1 / 20 : ℝ))
    (hu1 : 1 ≤ (M : ℝ) ^ (1 / 5 : ℝ)) :
    Real.exp (-(4 * ((M : ℝ) ^ (3 / 4 : ℝ) / ((1 + η) * M)) ^ 2 *
        (cG * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4)) /
        (((Nat.log 2 (2 * M) + 2) ^ 3 * B : ℕ) : ℝ))) ≤
      1 / (2 * (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ)) := by
  have hx : (0 : ℝ) < M := by exact_mod_cast hM
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the size of `Nat.log 2 (2 M)`
  have hk : ((Nat.log 2 (2 * M) : ℕ) : ℝ) ≤ 1 + 2 * Real.log M := by
    have h1 := Real.natLog_le_logb (2 * M) 2
    have h2 : Real.logb ((2 : ℕ) : ℝ) ((2 * M : ℕ) : ℝ) = 1 + Real.log M / Real.log 2 := by
      rw [Real.logb, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul two_ne_zero hx.ne', add_div,
        div_self hlog2pos.ne']
    have h3 : Real.log M / Real.log 2 ≤ 2 * Real.log M := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith [mul_le_mul_of_nonneg_left log_two_ge_half (by linarith : (0 : ℝ) ≤ Real.log M)]
    rw [h2] at h1
    linarith
  have hD0 : (0 : ℝ) < (((Nat.log 2 (2 * M) + 2) ^ 3 * B : ℕ) : ℝ) := by
    have : 0 < (Nat.log 2 (2 * M) + 2) ^ 3 * B := by positivity
    exact_mod_cast this
  have hD : (((Nat.log 2 (2 * M) + 2) ^ 3 * B : ℕ) : ℝ) ≤ 27 * Real.log M ^ 3 * B := by
    push_cast
    have h1 : ((Nat.log 2 (2 * M) : ℕ) : ℝ) + 2 ≤ 3 * Real.log M := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 3
    calc (((Nat.log 2 (2 * M) : ℕ) : ℝ) + 2) ^ 3 * B ≤ (3 * Real.log M) ^ 3 * B :=
          mul_le_mul_of_nonneg_right h2 hB'.le
      _ = 27 * Real.log M ^ 3 * B := by ring
  have hcore := clause7_core hx hη hη1 hcG hB' (by linarith) hD0 hD hr
  -- `log (2 P) ≤ 8 M^{1/5}`
  have hP : (0 : ℝ) < (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos _
  have h2P : (0 : ℝ) < 2 * (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ) := by linarith
  have hPlog : Real.log (2 * (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ)) ≤
      8 * (M : ℝ) ^ (1 / 5 : ℝ) := by
    rw [Real.log_mul two_ne_zero hP.ne', ← Chebyshev.psi_eq_log_lcmUpto,
      ← Chebyshev.psi_eq_psi_coe_floor]
    have h1 := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx.le (1 / 5 : ℝ))
    have h3 : (Real.log 4 + 4) * (M : ℝ) ^ (1 / 5 : ℝ) ≤ 7 * (M : ℝ) ^ (1 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [log_four_le_three]) (by positivity)
    linarith [log_two_le_one]
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le h2P ((Real.log_le_iff_le_exp h2P).mp (hPlog.trans hcore))

end AsymAux

open AsymAux

/-- All "for `M` large" facts used in the proof of Proposition 2. -/
lemma prop2_eventually (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (cG : ℝ) (hcG : 0 < cG) (B : ℕ)
    (hB : 0 < B) : ∀ᶠ M : ℕ in atTop,
    0 < M ∧
    2 * (M : ℝ) ^ (3 / 4 : ℝ) < (M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4 ∧
    (M : ℝ) ^ (3 / 4 : ℝ) < (M : ℝ) / 2 ∧
    (2 * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4) + 1) * ((⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ) + 1)
      / M ≤ (M : ℝ) ^ (-(1 / 21 : ℝ)) / 2 ∧
    (M : ℝ) ^ (3 / 4 : ℝ) / ((1 + η) * M) ≤ 1 / 2 ∧
    2 * (M : ℝ) ^ (3 / 4 : ℝ) < (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ) ∧
    Real.exp (-(4 * ((M : ℝ) ^ (3 / 4 : ℝ) / ((1 + η) * M)) ^ 2 *
        (cG * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4)) /
        (((Nat.log 2 (2 * M) + 2) ^ 3 * B : ℕ) : ℝ))) ≤
      1 / (2 * (Nat.lcmUpto ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ : ℝ)) ∧
    2 ≤ ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ := by
  filter_upwards [eventually_gt_atTop 0, ev_log_ge 4,
    ev_rpow_ge (s := 1 / 4) (by norm_num) 3,
    ev_rpow_ge (s := 1 / 5) (by norm_num) 12,
    ev_rpow_ge (s := 1 / 420) (by norm_num) 1,
    ev_log_pow_le 4 (s := 1 / 420) (by norm_num) (c := 1 / 12) (by norm_num),
    ev_log_pow_le 1 (s := 1 / 5) (by norm_num) (c := 1 / 4) (by norm_num),
    ev_rpow_ge (s := 1 / 20) (by norm_num) (216 * B / cG)]
    with M hM hL h4 h5 h420 hkey hlog5 h20
  have hx : (0 : ℝ) < M := by exact_mod_cast hM
  have h3 : (M : ℝ) ^ (3 / 4 : ℝ) < (M : ℝ) / 2 := clause3 hx h4
  rw [pow_one] at hlog5
  refine ⟨hM, clause2 hx (by linarith), h3,
    clause4 hx (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) (by linarith) h420 hkey,
    clause5 hx hη h3, clause6 hx h5 hlog5, clause7 hη hη1 hcG hB hM hL h20 (by linarith),
    Nat.le_floor ?_⟩
  exact_mod_cast (show (2 : ℝ) ≤ (M : ℝ) ^ (1 / 5 : ℝ) by linarith)

/-- The residual `x` produced by Proposition 1 is not too small for Proposition 2. -/
lemma main_eventually : ∀ᶠ N : ℕ in atTop,
    1 / (N : ℝ) + (N : ℝ) ^ (-(1 / 21 : ℝ)) ≤ 1 / (20 * Real.log N) := by
  filter_upwards [eventually_ge_atTop 3,
    ev_log_pow_le 1 (s := 1 / 21) (by norm_num) (c := 1 / 40) (by norm_num),
    ev_log_pow_le 1 (s := 1) (by norm_num) (c := 1 / 40) (by norm_num)] with N hN h1 h2
  have hx : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  rw [pow_one] at h1 h2
  rw [Real.rpow_one] at h2
  have hw : 0 < (N : ℝ) ^ (1 / 21 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith)]
  have e1 : 1 / (N : ℝ) ≤ 1 / (40 * Real.log N) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have e2 : ((N : ℝ) ^ (1 / 21 : ℝ))⁻¹ ≤ 1 / (40 * Real.log N) := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have e3 : 1 / (40 * Real.log N) + 1 / (40 * Real.log N) = 1 / (20 * Real.log N) := by
    ring
  linarith

end Croot
