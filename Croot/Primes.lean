import Croot.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Chebyshev-strength prime estimates used in the proof

All results follow from Mathlib's Chebyshev bounds
(`Chebyshev.theta_le_log4_mul_x`, `Chebyshev.theta_ge'`, `Chebyshev.pi_le_log4_mul_div`).

Helper lemmas:
* `Croot.eventually_log_pow_le_mul_sqrt`: `(log x) ^ n ≤ ε √x` eventually;
* `Croot.exists_sum_inv_primePow_Ioc_le`: a dyadic-block bound
  `∑_{q ∈ (A, B], q prime power} 1/q ≤ 12 (log B - log A + 2) / log A` for `A₀ ≤ A ≤ B`,
  deduced from `Croot.eventually_card_primePow_le`.
-/

namespace Croot

open Real Finset Filter

/-- For every `n` and every `ε > 0`, eventually `(log x) ^ n ≤ ε √x`. -/
lemma eventually_log_pow_le_mul_sqrt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ n ≤ ε * √x := by
  have h := (isLittleO_log_rpow_rpow_atTop (n : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound hε
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have e1 : ‖Real.log x ^ (n : ℝ)‖ = Real.log x ^ n := by
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog n)]
  have e2 : ‖x ^ (1 / 2 : ℝ)‖ = √x := by
    rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hx' : ‖Real.log x ^ (n : ℝ)‖ ≤ ε * ‖x ^ (1 / 2 : ℝ)‖ := hx
  rw [e1, e2] at hx'
  exact hx'

/-- For large `x` there are at least `x / (5 log x)` primes in `(x, 2.7 x]`. -/
theorem eventually_card_primes_Ioc_ge : ∀ᶠ x : ℝ in atTop,
    x / (5 * Real.log x) ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
  filter_upwards [eventually_ge_atTop (10 : ℝ),
    eventually_log_pow_le_mul_sqrt 1 (ε := 1 / 2000) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with x hx hlogx hL2
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hl2lo : (693 / 1000 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hfl : ⌊x⌋₊ ≤ ⌊(27 / 10 : ℝ) * x⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit : Chebyshev.theta ((27 / 10 : ℝ) * x) = Chebyshev.theta x +
      ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p := by
    simp only [Chebyshev.theta, Finset.sum_filter]
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
  have hsum : ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) *
        Real.log ((27 / 10 : ℝ) * x) := by
    have h := Finset.sum_le_card_nsmul ((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime)
      (fun p : ℕ => Real.log p) (Real.log ((27 / 10 : ℝ) * x)) (by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hpI := Finset.mem_Ioc.mp hp'.1
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
        have hp_le : (p : ℝ) ≤ (27 / 10 : ℝ) * x :=
          le_trans (by exact_mod_cast hpI.2) (Nat.floor_le (by linarith))
        exact Real.log_le_log hp_pos hp_le)
    rw [nsmul_eq_mul] at h
    exact h
  have hlow := Chebyshev.theta_ge' (x := (27 / 10 : ℝ) * x) (by linarith)
  have hup := Chebyshev.theta_le_log4_mul_x hx0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  rw [hlog4] at hup
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hss : √x * √x = x := Real.mul_self_sqrt hx0
  have hs3 : 3 ≤ √x := Real.le_sqrt_of_sq_le (by linarith)
  have hlogx' : Real.log x ≤ 1 / 2000 * √x := by simpa using hlogx
  have hlog27 : Real.log ((27 / 10 : ℝ) * x) ≤ Real.log x + 17 / 10 := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log (27 / 10 : ℝ) ≤ 27 / 10 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlog27' : 0 ≤ Real.log ((27 / 10 : ℝ) * x) := Real.log_nonneg (by linarith)
  have hlogx2 : Real.log ((27 / 10 : ℝ) * x + 2) ≤ Real.log x + 2 := by
    have h3x := Real.log_le_log (by linarith) (show (27 / 10 : ℝ) * x + 2 ≤ 3 * x by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3x
    have : Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hsqrt27 : √((27 / 10 : ℝ) * x) ≤ 2 * √x := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hx0]
  have hprod : √((27 / 10 : ℝ) * x) * Real.log ((27 / 10 : ℝ) * x) ≤
      (2 * √x) * (2 * Real.log x) :=
    mul_le_mul hsqrt27 (by linarith) hlog27' (by positivity)
  have hsL : √x * Real.log x ≤ √x * (1 / 2000 * √x) := mul_le_mul_of_nonneg_left hlogx' hs0
  have hsL3 : 3 ≤ √x * Real.log x := by nlinarith
  have hLsL : Real.log x ≤ √x * Real.log x := by nlinarith
  have hx2 : 693 / 1000 * x ≤ Real.log 2 * x := mul_le_mul_of_nonneg_right hl2lo.le hx0
  have hdiff : (48 / 100 : ℝ) * x ≤
      ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p := by
    linarith [hsplit, hlow, hup, hlogx2, hprod, hsL, hss, hsL3, hLsL, hx2]
  have hcard0 : (0 : ℝ) ≤ (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
    positivity
  have hc1 := mul_le_mul_of_nonneg_left hlog27 hcard0
  have hc2 := mul_nonneg hcard0 (show (0 : ℝ) ≤ 5 / 2 * Real.log x - 17 / 4 by linarith)
  rw [div_le_iff₀ (by linarith)]
  linarith [hsum, hdiff, hc1, hc2]

/-- For large `x` the number of prime powers in `[1, x]` is at most `4 x / log x`. -/
theorem eventually_card_primePow_le : ∀ᶠ x : ℝ in atTop,
    (((Icc 1 ⌊x⌋₊).filter IsPrimePow).card : ℝ) ≤ 4 * x / Real.log x := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_log_pow_le_mul_sqrt 2 (ε := 1 / 10) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx2 hlog2 hL1
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hl2lo : (693 / 1000 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hl2pos : 0 < Real.log 2 := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hIcc : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hcount := Chebyshev.sum_PrimePow_eq_sum_sum (fun _ => (1 : ℝ)) hx0
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcount
  have hK1 : 1 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hl2pos, one_mul]
    exact Real.log_le_log (by norm_num) hx2
  rw [← Finset.add_sum_Ioc_eq_sum_Icc hK1] at hcount
  simp only [Nat.cast_one, div_one, Real.rpow_one] at hcount
  have hπ : (((Ioc 0 ⌊x⌋₊).filter Nat.Prime).card : ℝ) ≤
      Real.log 4 * x / Real.log √x + √x := by
    rw [← Nat.primesLE_eq_filter_Ioc_zero, Nat.primesLE_card_eq_primeCounting]
    exact Chebyshev.pi_le_log4_mul_div hx1
  have hrest : ∑ k ∈ Ioc 1 ⌊Real.log x / Real.log 2⌋₊,
      (((Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime).card : ℝ) ≤
        (Real.log x / Real.log 2) * √x := by
    calc _ ≤ ∑ k ∈ Ioc 1 ⌊Real.log x / Real.log 2⌋₊, √x := by
          apply Finset.sum_le_sum
          intro k hk
          have hk2' : 2 ≤ k := (Finset.mem_Ioc.mp hk).1
          have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk2'
          calc (((Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime).card : ℝ)
              ≤ ((Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊).card : ℝ) := by
                exact_mod_cast Finset.card_filter_le _ _
            _ = (⌊x ^ (1 / (k : ℝ))⌋₊ : ℝ) := by rw [Nat.card_Ioc, Nat.sub_zero]
            _ ≤ x ^ (1 / (k : ℝ)) := Nat.floor_le (Real.rpow_nonneg hx0 _)
            _ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le
                (one_div_le_one_div_of_le (by norm_num) hk2)
            _ = √x := (Real.sqrt_eq_rpow x).symm
      _ = ((⌊Real.log x / Real.log 2⌋₊ - 1 : ℕ) : ℝ) * √x := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ (Real.log x / Real.log 2) * √x := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg x)
          calc ((⌊Real.log x / Real.log 2⌋₊ - 1 : ℕ) : ℝ)
              ≤ (⌊Real.log x / Real.log 2⌋₊ : ℝ) := by exact_mod_cast Nat.sub_le _ _
            _ ≤ Real.log x / Real.log 2 := Nat.floor_le (div_nonneg hL0.le hl2pos.le)
  have hsqrt_log : Real.log √x = Real.log x / 2 := Real.log_sqrt hx0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  rw [hsqrt_log, hlog4] at hπ
  have hπ' : (((Ioc 0 ⌊x⌋₊).filter Nat.Prime).card : ℝ) ≤
      4 * Real.log 2 * x / Real.log x + √x := by
    have e : 2 * Real.log 2 * x / (Real.log x / 2) = 4 * Real.log 2 * x / Real.log x := by
      ring
    linarith [hπ, e]
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hss : √x * √x = x := Real.mul_self_sqrt hx0
  have hdiv : Real.log x / Real.log 2 ≤ 2 * Real.log x := by
    rw [div_le_iff₀ hl2pos]; nlinarith
  have key : √x + (Real.log x / Real.log 2) * √x ≤ (4 - 4 * Real.log 2) * x / Real.log x := by
    rw [le_div_iff₀ hL0]
    have h0 : (Real.log x / Real.log 2) * √x ≤ (2 * Real.log x) * √x :=
      mul_le_mul_of_nonneg_right hdiv hs0
    have h1 : (√x + (Real.log x / Real.log 2) * √x) * Real.log x ≤
        (√x + 2 * Real.log x * √x) * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith) hL0.le
    have h2 : Real.log x ^ 2 * √x ≤ 1 / 10 * √x * √x := by
      have := mul_le_mul_of_nonneg_right hlog2 hs0
      linarith
    have h3 : 0 ≤ √x * Real.log x * (Real.log x - 1) :=
      mul_nonneg (mul_nonneg hs0 hL0.le) (by linarith)
    have h4 : Real.log 2 * x ≤ 7 / 10 * x := mul_le_mul_of_nonneg_right hl2hi.le hx0
    linarith [h1, h2, h3, h4, hss]
  rw [hIcc, hcount]
  have e2 : 4 * Real.log 2 * x / Real.log x + (4 - 4 * Real.log 2) * x / Real.log x =
      4 * x / Real.log x := by ring
  linarith [hπ', hrest, key, e2]

/-- Dyadic-block bound for reciprocal sums of prime powers. -/
lemma exists_sum_inv_primePow_Ioc_le : ∃ A₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → A ≤ B →
    ∑ q ∈ (Ioc A B).filter IsPrimePow, (1 : ℝ) / q ≤
      12 * (Real.log B - Real.log A + 2) / Real.log A := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp eventually_card_primePow_le
  refine ⟨max 2 ⌈X₀⌉₊, fun A B hA hAB => ?_⟩
  have hA2 : 2 ≤ A := le_trans (le_max_left _ _) hA
  have hAX : X₀ ≤ (A : ℝ) := by
    have h1 : ⌈X₀⌉₊ ≤ A := le_trans (le_max_right _ _) hA
    calc X₀ ≤ (⌈X₀⌉₊ : ℝ) := Nat.le_ceil X₀
      _ ≤ (A : ℝ) := by exact_mod_cast h1
  have hl2lo : (693 / 1000 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hl2pos : 0 < Real.log 2 := by linarith
  have hab : Nat.log 2 A ≤ Nat.log 2 B := Nat.log_mono_right hAB
  have hmaps : ∀ q ∈ (Ioc A B).filter IsPrimePow,
      Nat.log 2 q ∈ Icc (Nat.log 2 A) (Nat.log 2 B) := by
    intro q hq
    have hq' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
    exact Finset.mem_Icc.mpr ⟨Nat.log_mono_right hq'.1.le, Nat.log_mono_right hq'.2⟩
  have hblock : ∀ j ∈ Icc (Nat.log 2 A) (Nat.log 2 B),
      ∑ q ∈ (Ioc A B).filter IsPrimePow with Nat.log 2 q = j, (1 : ℝ) / q ≤
        8 / ((j + 1) * Real.log 2) := by
    intro j hj
    have hja : Nat.log 2 A ≤ j := (Finset.mem_Icc.mp hj).1
    have hX : X₀ ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by
      have h1 : A < 2 ^ (Nat.log 2 A).succ := Nat.lt_pow_succ_log_self (by norm_num) A
      have h2 : 2 ^ (Nat.log 2 A).succ ≤ 2 ^ (j + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : (A : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le h1 h2).le
      linarith
    have hcnt := hX₀ _ hX
    rw [Nat.floor_natCast] at hcnt
    have hsub : ((Ioc A B).filter IsPrimePow).filter (fun q => Nat.log 2 q = j) ⊆
        (Icc 1 (2 ^ (j + 1))).filter IsPrimePow := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, ?_⟩, hq.1.2⟩
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
      rw [hq.2] at this
      exact this.le
    have hD : (0 : ℝ) < (j + 1) * Real.log 2 := mul_pos (by positivity) hl2pos
    have hlogpow : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) = (j + 1) * Real.log 2 := by
      push_cast [Real.log_pow]; ring
    rw [hlogpow] at hcnt
    have hcard_le : ((((Ioc A B).filter IsPrimePow).filter (fun q => Nat.log 2 q = j)).card : ℝ)
        ≤ (((Icc 1 (2 ^ (j + 1))).filter IsPrimePow).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    calc ∑ q ∈ (Ioc A B).filter IsPrimePow with Nat.log 2 q = j, (1 : ℝ) / q
        ≤ ∑ q ∈ (Ioc A B).filter IsPrimePow with Nat.log 2 q = j, (1 : ℝ) / 2 ^ j := by
          apply Finset.sum_le_sum
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
          have hq0 : q ≠ 0 := by omega
          have h2q : 2 ^ j ≤ q := by
            have := Nat.pow_log_le_self 2 hq0
            rw [hq.2] at this
            exact this
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast h2q
      _ = ((((Ioc A B).filter IsPrimePow).filter (fun q => Nat.log 2 q = j)).card : ℝ) / 2 ^ j := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ (4 * ((2 ^ (j + 1) : ℕ) : ℝ) / ((j + 1) * Real.log 2)) / 2 ^ j :=
          div_le_div_of_nonneg_right (le_trans hcard_le hcnt) (by positivity)
      _ = 8 / ((j + 1) * Real.log 2) := by
          rw [div_div, div_eq_div_iff (mul_pos hD (by positivity)).ne' hD.ne']
          push_cast
          ring
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hlA : 0 < Real.log A := Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hAlt : Real.log A < (Nat.log 2 A + 1) * Real.log 2 := by
    have h1 : A < 2 ^ (Nat.log 2 A + 1) := Nat.lt_pow_succ_log_self (by norm_num) A
    have h2 : (A : ℝ) < 2 ^ (Nat.log 2 A + 1) := by exact_mod_cast h1
    have := Real.log_lt_log hA0 h2
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hBge : (Nat.log 2 B : ℝ) * Real.log 2 ≤ Real.log B := by
    have h1 : 2 ^ (Nat.log 2 B) ≤ B := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 : ℝ) ^ (Nat.log 2 B)) ≤ (B : ℝ) := by exact_mod_cast h1
    have := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at this
    exact this
  have hab' : (Nat.log 2 A : ℝ) ≤ Nat.log 2 B := by exact_mod_cast hab
  calc ∑ j ∈ Icc (Nat.log 2 A) (Nat.log 2 B),
        ∑ q ∈ (Ioc A B).filter IsPrimePow with Nat.log 2 q = j, (1 : ℝ) / q
      ≤ ∑ j ∈ Icc (Nat.log 2 A) (Nat.log 2 B), 8 / ((j + 1) * Real.log 2) :=
        Finset.sum_le_sum hblock
    _ ≤ ∑ j ∈ Icc (Nat.log 2 A) (Nat.log 2 B), 8 / ((Nat.log 2 A + 1) * Real.log 2) := by
        apply Finset.sum_le_sum
        intro j hj
        have hja : (Nat.log 2 A : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
        apply div_le_div_of_nonneg_left (by norm_num) (mul_pos (by positivity) hl2pos)
        exact mul_le_mul_of_nonneg_right (by linarith) hl2pos.le
    _ = ((Nat.log 2 B + 1 - Nat.log 2 A : ℕ) : ℝ) * (8 / ((Nat.log 2 A + 1) * Real.log 2)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ 12 * (Real.log B - Real.log A + 2) / Real.log A := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
        rw [mul_div_assoc', div_le_div_iff₀ (mul_pos (by positivity) hl2pos) hlA]
        have h1 : ((Nat.log 2 B : ℝ) + 1 - Nat.log 2 A) * Real.log 2 ≤
            Real.log B - Real.log A + 2 := by
          linarith [hBge, hAlt, hl2hi]
        have hu : (0 : ℝ) ≤ (Nat.log 2 B : ℝ) + 1 - Nat.log 2 A := by linarith
        have h2 := mul_le_mul_of_nonneg_left hAlt.le (mul_nonneg hu hl2pos.le)
        have h3 := mul_le_mul_of_nonneg_right h1
          (mul_pos (by positivity : (0 : ℝ) < (Nat.log 2 A : ℝ) + 1) hl2pos).le
        have h4 : (8 : ℝ) * (((Nat.log 2 B : ℝ) + 1 - Nat.log 2 A) * Real.log A) ≤
            12 * Real.log 2 * (((Nat.log 2 B : ℝ) + 1 - Nat.log 2 A) * Real.log A) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hu hlA.le)
        linarith [h2, h3, h4]

/-- The reciprocal sum of the prime powers in `(N / (log N)^4, 3 N]` tends to `0`. -/
theorem tendsto_sum_inv_primePow_Ioc :
    Tendsto (fun N : ℕ => ∑ q ∈ (Ioc ⌊(N : ℝ) / (Real.log N) ^ 4⌋₊ (3 * N)).filter IsPrimePow,
      (1 : ℝ) / q) atTop (nhds 0) := by
  obtain ⟨A₀, hA₀⟩ := exists_sum_inv_primePow_Ioc_le
  have hg : Tendsto (fun N : ℕ => 120 * (1 + Real.log (Real.log N)) / Real.log N)
      atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have h2 : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa using this
    have h3 : Tendsto (fun t : ℝ => 120 * (t⁻¹ + Real.log t / t)) atTop
        (nhds (120 * (0 + 0))) := (h1.add h2).const_mul 120
    rw [add_zero, mul_zero] at h3
    have h4 : Tendsto (fun t : ℝ => 120 * (1 + Real.log t) / t) atTop (nhds 0) :=
      h3.congr fun t => by ring
    exact (h4.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun N => Finset.sum_nonneg fun q _ => by positivity)
    ?_ hg
  have E1 : ∀ᶠ x : ℝ in atTop, 4 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 4
  have E2 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 4 ≤ 1 * √x := eventually_log_pow_le_mul_sqrt 4 one_pos
  have E3 : ∀ᶠ x : ℝ in atTop, ((A₀ : ℝ) + 2) ^ 2 ≤ x := eventually_ge_atTop _
  have E4 : ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ^ 1 ≤ 1 / 16 * √(Real.log x) :=
    Real.tendsto_log_atTop.eventually (eventually_log_pow_le_mul_sqrt 1 (by norm_num))
  have E5 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have hall := tendsto_natCast_atTop_atTop.eventually (E1.and (E2.and (E3.and (E4.and E5))))
  filter_upwards [hall] with N hN
  obtain ⟨h1, h2, h3, h4, h5⟩ := hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hL4pos : 0 < Real.log N ^ 4 := by positivity
  have hsq : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt hN0
  have hsq0 : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  have hsqrt_ge : (A₀ : ℝ) + 2 ≤ √(N : ℝ) := Real.le_sqrt_of_sq_le h3
  have hA₀0 : (0 : ℝ) ≤ A₀ := Nat.cast_nonneg _
  generalize hy : (N : ℝ) / Real.log N ^ 4 = y
  have hy_ge : √(N : ℝ) ≤ y := by
    rw [← hy, le_div_iff₀ hL4pos]
    have := mul_le_mul_of_nonneg_left h2 hsq0
    nlinarith
  have hy_le : y ≤ N := by
    rw [← hy]
    apply div_le_self hN0
    have : (1 : ℝ) ≤ Real.log N := by linarith
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
  have hy2 : 2 ≤ y := by linarith
  generalize hA : ⌊y⌋₊ = A
  have hA_ge : A₀ ≤ A := by
    rw [← hA]; apply Nat.le_floor; linarith
  have hA_real_le : (A : ℝ) ≤ y := by rw [← hA]; exact Nat.floor_le (by linarith)
  have hA_real_ge : y / 2 ≤ (A : ℝ) := by
    have := Nat.sub_one_lt_floor y
    rw [hA] at this
    linarith
  have hAB : A ≤ 3 * N := by
    have : (A : ℝ) ≤ 3 * N := by linarith
    exact_mod_cast this
  have hbound := hA₀ A (3 * N) hA_ge hAB
  have hApos : (0 : ℝ) < A := by linarith
  have hlogA_ge : Real.log N - 4 * Real.log (Real.log N) - Real.log 2 ≤ Real.log A := by
    have h := Real.log_le_log (by linarith) hA_real_ge
    rw [Real.log_div (by linarith) (by norm_num), ← hy,
      Real.log_div (by linarith) (by positivity), Real.log_pow] at h
    push_cast at h
    linarith
  have hlog3N : Real.log ((3 * N : ℕ) : ℝ) = Real.log 3 + Real.log N := by
    push_cast
    exact Real.log_mul (by norm_num) (by linarith)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hlog2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlogL0 : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hlogL : Real.log (Real.log N) ≤ Real.log N / 16 := by
    have hsqrtL : √(Real.log N) ≤ Real.log N :=
      (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
    rw [pow_one] at h4
    linarith
  have hlA_ge : Real.log N / 2 ≤ Real.log A := by linarith
  have hlA_pos : 0 < Real.log A := by linarith
  have hnum : Real.log ((3 * N : ℕ) : ℝ) - Real.log A + 2 ≤ 5 + 4 * Real.log (Real.log N) := by
    rw [hlog3N]; linarith
  calc _ ≤ 12 * (Real.log ((3 * N : ℕ) : ℝ) - Real.log A + 2) / Real.log A := hbound
    _ ≤ 120 * (1 + Real.log (Real.log N)) / Real.log N := by
      rw [div_le_div_iff₀ hlA_pos hL0]
      have k1 := mul_le_mul_of_nonneg_right hnum hL0.le
      have k2 := mul_le_mul_of_nonneg_left hlA_ge
        (by linarith : (0 : ℝ) ≤ 1 + Real.log (Real.log N))
      have k3 := mul_nonneg hlogL0 hL0.le
      linarith [k1, k2, k3]

end Croot
