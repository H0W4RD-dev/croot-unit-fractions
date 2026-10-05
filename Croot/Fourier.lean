import Croot.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Finite Fourier analysis for subset sums of unit fractions

`eC t = exp (2 π i t)`.  For a finite set `Y` of positive integers dividing `P` and a rational
`x` with `x P ∈ ℤ`, summing `e(-h x) ∏_{m∈Y} (1 + e(h/m))` over any `P` consecutive integers `h`
counts (times `P`) the subsets `Z ⊆ Y` with `∑_{m∈Z} 1/m - x ∈ ℤ`.  We also record the
elementary estimates on the individual terms used in Croot's Proposition 2.
-/

namespace Croot

open Real Complex Finset

/-- `e(t) = exp(2 π i t)`. -/
noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-! ### Basic properties of `eC` -/

lemma eC_add (s t : ℝ) : eC (s + t) = eC s * eC t := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eC_zero : eC 0 = 1 := by
  simp [eC]

lemma eC_eq_one_iff (t : ℝ) : eC t = 1 ↔ ∃ n : ℤ, t = n := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h3 : (t : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]
      ring
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

lemma eC_intCast (n : ℤ) : eC n = 1 := (eC_eq_one_iff _).2 ⟨n, rfl⟩

lemma norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  have : (2 * (π : ℂ) * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma eC_re (t : ℝ) : (eC t).re = Real.cos (2 * π * t) := by
  unfold eC
  have : (2 * (π : ℂ) * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

lemma eC_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    eC (∑ i ∈ s, f i) = ∏ i ∈ s, eC (f i) := by
  unfold eC
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

lemma eC_nat_mul (n : ℕ) (t : ℝ) : eC (n * t) = eC t ^ n := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `1 + e(θ) = e(θ/2) · 2 cos(π θ)`. -/
lemma one_add_eC (θ : ℝ) :
    1 + eC θ = eC (θ / 2) * ((2 * Real.cos (π * θ) : ℝ) : ℂ) := by
  have h1 : ((2 * Real.cos (π * θ) : ℝ) : ℂ) =
      Complex.exp (((π * θ : ℝ) : ℂ) * I) + Complex.exp (-((π * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.two_cos]
    push_cast
    rfl
  rw [h1, mul_add]
  unfold eC
  rw [← Complex.exp_add, ← Complex.exp_add]
  have e1 : 2 * (π : ℂ) * I * ((θ / 2 : ℝ) : ℂ) + ((π * θ : ℝ) : ℂ) * I = 2 * π * I * θ := by
    push_cast
    ring
  have e2 : 2 * (π : ℂ) * I * ((θ / 2 : ℝ) : ℂ) + -((π * θ : ℝ) : ℂ) * I = 0 := by
    push_cast
    ring
  rw [e1, e2, Complex.exp_zero, add_comm]

lemma norm_one_add_eC (θ : ℝ) : ‖1 + eC θ‖ = 2 * |Real.cos (π * θ)| := by
  rw [one_add_eC, norm_mul, norm_eC, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_two]

lemma norm_one_add_eC_le_two (θ : ℝ) : ‖1 + eC θ‖ ≤ 2 := by
  calc ‖1 + eC θ‖ ≤ ‖(1 : ℂ)‖ + ‖eC θ‖ := norm_add_le _ _
    _ = 2 := by rw [norm_one, norm_eC]; norm_num

/-- `cos (π u) ≤ 1 - 4 u²` for `0 ≤ u ≤ 1/2`: Taylor bound for `u ≤ 3/10`, and
`cos (π u) = sin (π (1/2 - u)) ≤ π (1/2 - u)` for `u ≥ 3/10`. -/
lemma cos_pi_mul_le (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    Real.cos (π * u) ≤ 1 - 4 * u ^ 2 := by
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  rcases le_or_gt u (3 / 10) with hu | hu
  · have hpu : 0 ≤ π * u := by positivity
    have hx : |π * u| ≤ 1 := by
      rw [abs_of_nonneg hpu]
      nlinarith
    have hb := Real.cos_bound hx
    rw [abs_of_nonneg hpu] at hb
    have hb' := (abs_le.mp hb).2
    have hp2 : 9.85 ≤ π ^ 2 := by nlinarith
    have hp2' : π ^ 2 ≤ 9.93 := by nlinarith
    have hu2 : u ^ 2 ≤ 9 / 100 := by nlinarith
    have hu2' : 0 ≤ u ^ 2 := by positivity
    have hq1 : (u ^ 2) ^ 2 ≤ 9 / 100 * u ^ 2 := by nlinarith
    have hq2 : (π ^ 2) ^ 2 ≤ 9.93 ^ 2 := by nlinarith
    have h4 : (π * u) ^ 4 ≤ 9.93 ^ 2 * (9 / 100 * u ^ 2) := by
      have : (π * u) ^ 4 = (π ^ 2) ^ 2 * (u ^ 2) ^ 2 := by ring
      rw [this]
      exact mul_le_mul hq2 hq1 (by positivity) (by positivity)
    have h5 : 9.85 * u ^ 2 ≤ (π * u) ^ 2 := by
      have : (π * u) ^ 2 = π ^ 2 * u ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hp2 hu2'
    nlinarith
  · have hc : Real.cos (π * u) = Real.sin (π / 2 - π * u) := (Real.sin_pi_div_two_sub _).symm
    rw [hc]
    have hs := Real.sin_le (by nlinarith : 0 ≤ π / 2 - π * u)
    have hm : 0 ≤ (1 / 2 - u) * (2 + 4 * u - π) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- If `θ` is at distance `≥ δ` from every integer, then `‖1 + e(θ)‖ ≤ 2 (1 - 4 δ²)`. -/
lemma norm_one_add_eC_le_of_far (θ δ : ℝ) (hδ : 0 ≤ δ) (hfar : ∀ j : ℤ, δ ≤ |θ - j|) :
    ‖1 + eC θ‖ ≤ 2 * (1 - 4 * δ ^ 2) := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, |θ - j| ≤ 1 / 2 := ⟨round θ, abs_sub_round θ⟩
  have hδd : δ ≤ |θ - j| := hfar j
  have heq : eC θ = eC (θ - j) := by
    conv_lhs => rw [show θ = (θ - j) + (j : ℝ) by ring]
    rw [eC_add, eC_intCast, mul_one]
  rw [heq, norm_one_add_eC]
  have hcos : |Real.cos (π * (θ - j))| = Real.cos (π * |θ - j|) := by
    rw [← Real.cos_abs (π * (θ - j)), abs_mul, abs_of_pos Real.pi_pos]
    apply abs_of_nonneg
    have hle : π * |θ - j| ≤ π * (1 / 2) := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
    have hge : 0 ≤ π * |θ - j| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith [Real.pi_pos]
  rw [hcos]
  have hc := cos_pi_mul_le |θ - j| (abs_nonneg _) hj
  have hsq : δ * δ ≤ |θ - j| * |θ - j| := mul_le_mul hδd hδd hδ (abs_nonneg _)
  nlinarith

/-! ### Integrality and the window sum -/

lemma recipSum_mul_natCast_int (Z : Finset ℕ) (P : ℕ) (hZ : ∀ m ∈ Z, m ∣ P) :
    ∃ z : ℤ, recipSum Z * P = z := by
  refine ⟨∑ m ∈ Z, ((P / m : ℕ) : ℤ), ?_⟩
  rw [recipSum, Finset.sum_mul, Int.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Int.cast_natCast, Nat.cast_div_charZero (hZ m hm)]
  ring

open scoped Classical in
/-- A complete geometric sum over a window of `P` consecutive integers. -/
lemma sum_Ico_eC (r : ℝ) (P : ℕ) (hr : eC (P * r) = 1) (h₀ : ℤ) :
    ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC ((h : ℝ) * r) =
      if ∃ k : ℤ, r = k then (P : ℂ) else 0 := by
  have hre : ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC ((h : ℝ) * r) =
      ∑ k ∈ Finset.range P, eC ((h₀ : ℝ) * r) * eC r ^ k := by
    refine Finset.sum_nbij' (fun h => (h - h₀).toNat) (fun k => h₀ + k) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_Ico, Finset.mem_range] at hh ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
      omega
    · intro h hh
      simp only [Finset.mem_Ico] at hh ⊢
      omega
    · intro k _
      omega
    · intro h hh
      simp only [Finset.mem_Ico] at hh
      rw [← eC_nat_mul, ← eC_add]
      congr 1
      have h1 : (((h - h₀).toNat : ℕ) : ℝ) = (h : ℝ) - h₀ := by
        have : (((h - h₀).toNat : ℕ) : ℤ) = h - h₀ := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      rw [h1]
      ring
  rw [hre, ← Finset.mul_sum]
  split_ifs with hk
  · obtain ⟨k, rfl⟩ := hk
    have e1 : eC (k : ℝ) = 1 := eC_intCast k
    have e2 : eC ((h₀ : ℝ) * k) = 1 := by
      rw [show ((h₀ : ℝ) * k) = ((h₀ * k : ℤ) : ℝ) by push_cast; ring]
      exact eC_intCast _
    simp [e1, e2]
  · have hne : eC r ≠ 1 := fun h1 => hk ((eC_eq_one_iff r).1 h1)
    rw [geom_sum_eq hne, ← eC_nat_mul, hr]
    simp

-- `hP` is part of the fixed statement but not needed (for `P = 0` both sides vanish).
set_option linter.unusedVariables false in
open scoped Classical in
/-- The counting identity, over any window of `P` consecutive integers. -/
theorem fourier_count (Y : Finset ℕ) (P : ℕ) (hP : 0 < P) (hY : ∀ m ∈ Y, 0 < m ∧ m ∣ P)
    (x : ℚ) (hx : ∃ z : ℤ, x * P = z) (h₀ : ℤ) :
    ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m)) =
      (P : ℂ) * ((Y.powerset.filter (fun Z => ∃ k : ℤ, recipSum Z - x = k)).card : ℂ) := by
  -- expand the product over subsets and combine the exponentials
  have key : ∀ h : ℤ, eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m)) =
      ∑ Z ∈ Y.powerset, eC ((h : ℝ) * ((recipSum Z - x : ℚ) : ℝ)) := by
    intro h
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [← eC_sum, ← eC_add]
    congr 1
    simp only [recipSum, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    rw [mul_sub, Finset.mul_sum]
    simp only [mul_one_div]
    ring
  rw [Finset.sum_congr rfl fun h _ => key h, Finset.sum_comm, Finset.natCast_card_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z hZ => ?_
  -- for each subset `Z`, `(recipSum Z - x) * P` is an integer
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := recipSum_mul_natCast_int Z P
    (fun m hm => (hY m (Finset.mem_powerset.1 hZ hm)).2)
  have hq : (recipSum Z - x) * P = ((w - z : ℤ) : ℚ) := by
    rw [sub_mul, hw, hz, Int.cast_sub]
  have hr' : (P : ℝ) * ((recipSum Z - x : ℚ) : ℝ) = ((w - z : ℤ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hq
    push_cast at this ⊢
    linarith
  have hr : eC ((P : ℝ) * ((recipSum Z - x : ℚ) : ℝ)) = 1 := by
    rw [hr']
    exact eC_intCast _
  rw [sum_Ico_eC _ P hr h₀]
  have hiff : (∃ k : ℤ, ((recipSum Z - x : ℚ) : ℝ) = k) ↔ (∃ k : ℤ, recipSum Z - x = k) := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by exact_mod_cast hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; push_cast; rfl⟩
  by_cases hc : ∃ k : ℤ, recipSum Z - x = k
  · rw [if_pos (hiff.2 hc), if_pos hc, mul_one]
  · rw [if_neg (fun h' => hc (hiff.1 h')), if_neg hc, mul_zero]

/-- The `h = 0` term. -/
theorem term_zero (Y : Finset ℕ) (x : ℚ) :
    eC (-(((0 : ℤ) : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC (((0 : ℤ) : ℝ) / m)) = (2 : ℂ) ^ Y.card := by
  simp only [Int.cast_zero, zero_mul, neg_zero, zero_div, eC_zero, one_mul, Finset.prod_const]
  norm_num

/-- Terms with small `|h|` have nonnegative real part. -/
theorem re_term_nonneg (Y : Finset ℕ) (x : ℚ) (h : ℤ)
    (hY : ∀ m ∈ Y, 0 < m ∧ 2 * |(h : ℝ)| ≤ m)
    (hsmall : |(h : ℝ) * ((recipSum Y : ℝ) / 2 - (x : ℝ))| ≤ 1 / 4) :
    0 ≤ (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m))).re := by
  -- the term is `e(h (recipSum Y / 2 - x)) * ∏ 2 cos (π h / m)`
  simp_rw [one_add_eC]
  rw [Finset.prod_mul_distrib, ← eC_sum, ← mul_assoc, ← eC_add, ← Complex.ofReal_prod,
    Complex.re_mul_ofReal]
  apply mul_nonneg
  · rw [eC_re]
    have hsum : ∑ m ∈ Y, (h : ℝ) / m / 2 = (h : ℝ) * (∑ m ∈ Y, (1 : ℝ) / m) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    have hrs : ((recipSum Y : ℚ) : ℝ) = ∑ m ∈ Y, (1 : ℝ) / m := by
      simp only [recipSum, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    have hphi : -((h : ℝ) * (x : ℝ)) + ∑ m ∈ Y, (h : ℝ) / m / 2 =
        (h : ℝ) * ((recipSum Y : ℝ) / 2 - (x : ℝ)) := by
      rw [hsum, hrs]
      ring
    rw [hphi]
    obtain ⟨h1, h2⟩ := abs_le.mp hsmall
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
  · apply Finset.prod_nonneg
    intro m hm
    obtain ⟨hm0, hm1⟩ := hY m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    have habs : |(h : ℝ) / m| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hm', div_le_iff₀ hm']
      linarith
    obtain ⟨h1, h2⟩ := abs_le.mp habs
    apply mul_nonneg (by norm_num)
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]

/-- Norm bound: factors with `h/m` at distance `≥ δ` from every integer save `1 - 4 δ²`. -/
theorem norm_term_le (Y J : Finset ℕ) (hJ : J ⊆ Y) (x : ℚ) (h : ℤ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ 1 / 2) (hfar : ∀ m ∈ J, ∀ j : ℤ, δ ≤ |(h : ℝ) / m - j|) :
    ‖eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m))‖ ≤
      2 ^ Y.card * (1 - 4 * δ ^ 2) ^ J.card := by
  rw [norm_mul, norm_eC, one_mul, norm_prod, ← Finset.prod_sdiff hJ]
  have hc : 0 ≤ 1 - 4 * δ ^ 2 := by nlinarith
  have h1 : ∏ m ∈ Y \ J, ‖1 + eC ((h : ℝ) / m)‖ ≤ 2 ^ (Y \ J).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun m _ => norm_one_add_eC_le_two _)
  have h2 : ∏ m ∈ J, ‖1 + eC ((h : ℝ) / m)‖ ≤ (2 * (1 - 4 * δ ^ 2)) ^ J.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun m hm => norm_one_add_eC_le_of_far _ _ hδ (hfar m hm))
  calc (∏ m ∈ Y \ J, ‖1 + eC ((h : ℝ) / m)‖) * ∏ m ∈ J, ‖1 + eC ((h : ℝ) / m)‖
      ≤ 2 ^ (Y \ J).card * (2 * (1 - 4 * δ ^ 2)) ^ J.card :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = 2 ^ Y.card * (1 - 4 * δ ^ 2) ^ J.card := by
        rw [mul_pow, ← mul_assoc, ← pow_add, Finset.card_sdiff_add_card_eq_card hJ]

end Croot
