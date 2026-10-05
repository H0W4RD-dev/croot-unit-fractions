import Croot.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.ZMod.Basic

/-!
# Croot's Lemma 1: subset sums of inverses of primes cover all residues

For `n` large, if `R` is a set of at least `(log n)^{3.9}` primes in
`[(log n)^4/4, 3 (log n)^4]`, none dividing `n`, then every residue class modulo `n`
is a sum `∑_{r ∈ T} r⁻¹` over some subset `T ⊆ R`.

## Proof outline

Write `ψ = ZMod.stdAddChar` (`ψ x = exp (2πi x / n)`), `k = |R|` and `w = (log n)^{1/10}`, so
that `log n = w^10`, `(log n)^4 = w^40`, `(log n)^{3.9} = w^39`.

* `Lemma1Aux.exists_subset_sum_of_norm_prod_le` (Fourier criterion): by orthogonality,
  `∑_h ψ(-hc) ∏_{r∈R} (1 + ψ(h r⁻¹)) = n · #{T ⊆ R : ∑_{T} r⁻¹ = c}`; the `h = 0` term is
  `2^k`, so if every other term has norm `≤ 2^k / n` the count is positive.
* `Lemma1Aux.norm_one_add_stdAddChar_sq_le`: `‖1 + ψ x‖² ≤ 4 - 16 (t/n)²`, where `t` is the
  least absolute residue of `x` (from `cos θ ≤ 1 - 2θ²/π²` on `[-π, π]`).
* `Lemma1Aux.pow_card_le_of_primes_dvd`, `Lemma1Aux.card_bad_le` (pigeonhole): writing
  `t_r` for the least absolute residue of `h r⁻¹`, we have `r t_r = h + s_r n`; the primes with
  `|r t_r| ≤ L n` (`L = (log n)^{2.8} = w^28`) have `|s_r| ≤ L + 1`, and for each value of `s_r`
  the corresponding primes all divide the nonzero integer `h + s_r n` of size `< (L + 2) n`,
  so there are at most `2 log n` of them.  Hence at most `k/2` primes are "bad".
* `Lemma1Aux.norm_prod_le`: each good prime has `|t_r| / n ≥ 1 / (3 w^12)`, so its factor
  satisfies `‖1 + ψ‖² ≤ 4 exp(-4/(9 w^24))`; multiplying gives
  `‖∏‖² ≤ 4^k exp(-(2/9) w^15) ≤ 4^k / n²`.
* `Lemma1Aux.ineq_*`: the elementary inequalities in `w` (valid for `w ≥ 10`).
-/

namespace Croot

open Real Finset Filter

namespace Lemma1Aux

/-! ### Step 1: the Fourier-analytic existence criterion -/

section Fourier

variable {n : ℕ} [NeZero n]

/-- An additive character turns finite sums into products. -/
lemma stdAddChar_sum {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ZMod n) :
    ZMod.stdAddChar (∑ i ∈ T, f i) = ∏ i ∈ T, ZMod.stdAddChar (f i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- Fourier criterion: if every nontrivial frequency `h` gives a product of norm at most
`2^|R| / n`, then every residue class is a subset sum of the `u i`. -/
theorem exists_subset_sum_of_norm_prod_le {ι : Type*} [DecidableEq ι] (R : Finset ι)
    (u : ι → ZMod n)
    (hbound : ∀ h : ZMod n, h ≠ 0 →
      ‖∏ i ∈ R, (1 + ZMod.stdAddChar (h * u i))‖ ≤ 2 ^ R.card / n)
    (c : ZMod n) : ∃ T ⊆ R, ∑ i ∈ T, u i = c := by
  by_contra hne
  push Not at hne
  set F : ZMod n → ℂ := fun h =>
    ZMod.stdAddChar (-(h * c)) * ∏ i ∈ R, (1 + ZMod.stdAddChar (h * u i)) with hF
  have hexpand : ∀ h : ZMod n,
      F h = ∑ T ∈ R.powerset, ZMod.stdAddChar (h * (∑ i ∈ T, u i - c)) := by
    intro h
    simp only [hF]
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← stdAddChar_sum T (fun i => h * u i), ← AddChar.map_add_eq_mul]
    congr 1
    rw [mul_sub, Finset.mul_sum]
    ring
  have key : ∑ h : ZMod n, F h = 0 := by
    rw [Finset.sum_congr rfl fun h _ => hexpand h, Finset.sum_comm]
    refine Finset.sum_eq_zero fun T hT => ?_
    have hT' : ∑ i ∈ T, u i - c ≠ 0 := sub_ne_zero.2 (hne T (Finset.mem_powerset.1 hT))
    have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod n) ℂ))
      (∑ i ∈ T, u i - c) (ZMod.isPrimitive_stdAddChar n)
    rw [if_neg hT', Nat.cast_zero] at this
    exact this
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ (0 : ZMod n))] at key
  have h0 : F 0 = 2 ^ R.card := by
    simp only [hF, zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul, Finset.prod_const]
    norm_num
  rw [h0] at key
  set S := ∑ h ∈ Finset.univ.erase (0 : ZMod n), F h with hS
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  have hSnorm : ‖S‖ ≤ ((n : ℝ) - 1) * (2 ^ R.card / n) := by
    calc ‖S‖ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod n), ‖F h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod n), (2 ^ R.card / n : ℝ) := by
        refine Finset.sum_le_sum fun h hh => ?_
        simp only [hF]
        rw [norm_mul, AddChar.norm_apply, one_mul]
        exact hbound h (Finset.ne_of_mem_erase hh)
    _ = ((n : ℝ) - 1) * (2 ^ R.card / n) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          ZMod.card, nsmul_eq_mul, Nat.cast_sub NeZero.one_le, Nat.cast_one]
  have hSeq : S = -(2 : ℂ) ^ R.card := by linear_combination key
  rw [hSeq, norm_neg, norm_pow, Complex.norm_two] at hSnorm
  have h2 : (0 : ℝ) < 2 ^ R.card := by positivity
  have hlt : ((n : ℝ) - 1) * (2 ^ R.card / n) < 2 ^ R.card := by
    rw [mul_div_assoc', div_lt_iff₀ hn]
    nlinarith
  linarith

/-- `‖1 + e(x/n)‖² ≤ 4 - 16 (t/n)²`, where `t` is the least absolute residue of `x`. -/
lemma norm_one_add_stdAddChar_sq_le (x : ZMod n) :
    ‖1 + ZMod.stdAddChar x‖ ^ 2 ≤ 4 - 16 * ((x.valMinAbs : ℝ) / n) ^ 2 := by
  set t := x.valMinAbs with ht
  have hx : ((t : ℤ) : ZMod n) = x := ZMod.coe_valMinAbs x
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  set θ : ℝ := 2 * π * t / n with hθ
  have hpsi : ZMod.stdAddChar x = Complex.exp (θ * Complex.I) := by
    rw [← hx, ZMod.stdAddChar_coe]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hθbound : |θ| ≤ π := by
    obtain ⟨h1, h2⟩ := ZMod.valMinAbs_mem_Ioc x
    have h1' : -(n : ℝ) < t * 2 := by exact_mod_cast h1
    have h2' : (t : ℝ) * 2 ≤ n := by exact_mod_cast h2
    rw [abs_le]
    constructor
    · rw [hθ, le_div_iff₀ hn]
      nlinarith [pi_pos]
    · rw [hθ, div_le_iff₀ hn]
      nlinarith [pi_pos]
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθbound
  have hnorm : ‖1 + Complex.exp (θ * Complex.I)‖ ^ 2 = 2 + 2 * Real.cos θ := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [show (1 : ℂ) + (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I)
        = ↑(1 + Real.cos θ) + ↑(Real.sin θ) * Complex.I by push_cast; ring]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    linear_combination Real.sin_sq_add_cos_sq θ
  rw [hpsi, hnorm]
  have : 2 / π ^ 2 * θ ^ 2 = 8 * ((t : ℝ) / n) ^ 2 := by
    rw [hθ]
    field_simp
    ring
  linarith

end Fourier

/-! ### Step 2: few primes of size `≥ y` divide a nonzero integer -/

lemma pow_card_le_of_primes_dvd (A : Finset ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hA : ∀ a ∈ A, a.Prime ∧ y ≤ a) (z : ℤ) (hz : z ≠ 0) (hdvd : ∀ a ∈ A, (a : ℤ) ∣ z) :
    y ^ A.card ≤ |(z : ℝ)| := by
  have h1 : ∏ a ∈ A, a ∣ z.natAbs := by
    apply Finset.prod_primes_dvd
    · intro a ha
      exact (hA a ha).1.prime
    · intro a ha
      exact Int.ofNat_dvd_left.1 (hdvd a ha)
  have h2 : ∏ a ∈ A, a ≤ z.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hz) h1
  calc y ^ A.card = ∏ a ∈ A, y := (Finset.prod_const y).symm
  _ ≤ ∏ a ∈ A, (a : ℝ) := Finset.prod_le_prod (fun _ _ => hy) (fun a ha => (hA a ha).2)
  _ = ((∏ a ∈ A, a : ℕ) : ℝ) := by push_cast; rfl
  _ ≤ (z.natAbs : ℝ) := by exact_mod_cast h2
  _ = |(z : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

/-- The pigeonhole step: few `r` have `|r t_r|` small. -/
lemma card_bad_le (n H : ℕ) (hH0 : 0 < H) (hHn : H < n)
    (R : Finset ℕ) (y : ℝ) (hy : 1 ≤ y) (hR : ∀ r ∈ R, r.Prime ∧ y ≤ r)
    (t : ℕ → ℤ) (ht : ∀ r ∈ R, (n : ℤ) ∣ r * t r - H)
    (L : ℝ) (hL : 0 ≤ L) (m : ℕ) (hm : (L + 2) * n < y ^ (m + 1)) :
    ((R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card : ℝ) ≤ (2 * (L + 1) + 1) * m := by
  set M : ℤ := ⌊L + 1⌋ with hM
  have hM0 : 0 ≤ M := Int.floor_nonneg.2 (by linarith)
  have hML : (M : ℝ) ≤ L + 1 := Int.floor_le _
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hHn)
  have hHnR : (H : ℝ) < n := by exact_mod_cast hHn
  have hH0R : (0 : ℝ) < H := by exact_mod_cast hH0
  -- each fibre is small
  have hfib : ∀ v ∈ Finset.Icc (-M) M,
      (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card ≤ m := by
    intro v hv
    rw [Finset.mem_Icc] at hv
    have hvR : |(v : ℝ)| ≤ L + 1 := by
      rw [abs_le]
      have h1 : ((-M : ℤ) : ℝ) ≤ v := by exact_mod_cast hv.1
      have h2 : (v : ℝ) ≤ (M : ℝ) := by exact_mod_cast hv.2
      push_cast at h1
      constructor <;> linarith
    have hz : (H : ℤ) + n * v ≠ 0 := by
      intro h0
      have h0' : (H : ℝ) + n * v = 0 := by exact_mod_cast h0
      rcases le_or_gt 0 (v : ℝ) with hv0 | hv0
      · nlinarith
      · have : (v : ℝ) ≤ -1 := by
          have : v ≤ -1 := by
            have : v < 0 := by exact_mod_cast hv0
            omega
          exact_mod_cast this
        nlinarith
    have hzabs : |(((H : ℤ) + n * v : ℤ) : ℝ)| < (L + 2) * n := by
      push_cast
      calc |(H : ℝ) + n * v| ≤ |(H : ℝ)| + |(n : ℝ) * v| := abs_add_le _ _
      _ = H + n * |(v : ℝ)| := by
          rw [abs_mul, abs_of_nonneg hH0R.le, abs_of_nonneg hn.le]
      _ < n + n * (L + 1) := by nlinarith
      _ = (L + 2) * n := by ring
    have hpow := pow_card_le_of_primes_dvd (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)) y
      (by linarith)
      (fun r hr => hR r (Finset.mem_filter.1 hr).1) _ hz (fun r hr => (Finset.mem_filter.1 hr).2)
    by_contra hcon
    push Not at hcon
    have : y ^ (m + 1) ≤ y ^ (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card :=
      pow_le_pow_right₀ hy hcon
    linarith
  -- the bad set is covered by the fibres
  have hsub : R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) ⊆
      (Finset.Icc (-M) M).biUnion (fun v => R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrR, hrbad⟩ := hr
    obtain ⟨v, hv⟩ := ht r hrR
    have hvR : ((r : ℝ) * t r - H) = n * v := by exact_mod_cast hv
    rw [Finset.mem_biUnion]
    refine ⟨v, ?_, ?_⟩
    · have h1 : (n : ℝ) * |(v : ℝ)| < (L + 1) * n := by
        calc (n : ℝ) * |(v : ℝ)| = |(n : ℝ) * v| := by rw [abs_mul, abs_of_pos hn]
        _ = |(r : ℝ) * t r - H| := by rw [hvR]
        _ ≤ |(r : ℝ) * t r| + |(H : ℝ)| := abs_sub _ _
        _ < L * n + n := by rw [abs_of_nonneg hH0R.le]; linarith
        _ = (L + 1) * n := by ring
      have h2 : |(v : ℝ)| < L + 1 := by
        by_contra hcon
        push Not at hcon
        nlinarith
      rw [abs_lt] at h2
      rw [Finset.mem_Icc]
      constructor
      · have : -v ≤ M := Int.le_floor.2 (by push_cast; linarith)
        linarith
      · exact Int.le_floor.2 (by linarith)
    · rw [Finset.mem_filter]
      refine ⟨hrR, ⟨t r, ?_⟩⟩
      linear_combination -hv
  have hcard : (R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card ≤ (2 * M.toNat + 1) * m := by
    calc (R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card
        ≤ ((Finset.Icc (-M) M).biUnion
            (fun v => R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v))).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ Finset.Icc (-M) M, (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ v ∈ Finset.Icc (-M) M, m := Finset.sum_le_sum hfib
    _ = (2 * M.toNat + 1) * m := by
        rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
        congr 1
        omega
  have hMnat : ((M.toNat : ℕ) : ℝ) = (M : ℝ) := by
    have : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hM0
    exact_mod_cast this
  calc ((R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card : ℝ)
      ≤ (((2 * M.toNat + 1) * m : ℕ) : ℝ) := by exact_mod_cast hcard
  _ = (2 * (M : ℝ) + 1) * m := by push_cast; rw [hMnat]
  _ ≤ (2 * (L + 1) + 1) * m := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      linarith

/-! ### Step 3: elementary inequalities for large `w` -/

lemma ineq_bad (w : ℝ) (hw : 10 ≤ w) :
    (2 * (w ^ 28 + 1) + 1) * (2 * w ^ 10) ≤ w ^ 39 / 2 := by
  have h10 : 0 < w ^ 10 := by positivity
  have h28 : 6 ≤ w ^ 28 := by
    calc (6 : ℝ) ≤ 10 ^ 28 := by norm_num
    _ ≤ w ^ 28 := pow_le_pow_left₀ (by norm_num) hw 28
  have e1 : w ^ 38 = w ^ 28 * w ^ 10 := by ring
  have e2 : w ^ 39 = w * w ^ 38 := by ring
  have h38 : 6 * w ^ 10 ≤ w ^ 38 := by rw [e1]; nlinarith
  have h38' : 0 ≤ w ^ 38 := by positivity
  have h39 : 10 * w ^ 38 ≤ w ^ 39 := by rw [e2]; nlinarith
  have : (2 * (w ^ 28 + 1) + 1) * (2 * w ^ 10) = 4 * w ^ 38 + 6 * w ^ 10 := by ring
  rw [this]
  linarith

lemma ineq_good (w : ℝ) (hw : 10 ≤ w) :
    2 * w ^ 10 ≤ (w ^ 39 / 2) * (4 / (9 * w ^ 24)) := by
  have hw0 : 0 < w := by linarith
  have e : (w ^ 39 / 2) * (4 / (9 * w ^ 24)) = 2 / 9 * w ^ 15 := by
    field_simp
    ring
  rw [e]
  have h5 : 9 ≤ w ^ 5 := by
    calc (9 : ℝ) ≤ 10 ^ 5 := by norm_num
    _ ≤ w ^ 5 := pow_le_pow_left₀ (by norm_num) hw 5
  have e2 : w ^ 15 = w ^ 5 * w ^ 10 := by ring
  rw [e2]
  have h10 : 0 < w ^ 10 := by positivity
  nlinarith

lemma ineq_exp (w : ℝ) (hw : 10 ≤ w) : w ^ 28 + 2 ≤ Real.exp (w ^ 10) := by
  have h := Real.pow_div_factorial_le_exp (w ^ 10) (by positivity) 3
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h
  have e : (w ^ 10) ^ 3 = w ^ 2 * w ^ 28 := by ring
  rw [e] at h
  have h2 : 100 ≤ w ^ 2 := by nlinarith
  have h28 : 1 ≤ w ^ 28 := one_le_pow₀ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ w ^ 28)]

lemma ineq_e (w : ℝ) (hw : 10 ≤ w) : Real.exp 1 ≤ w ^ 40 / 4 := by
  have h := Real.exp_one_lt_three
  have : (10 : ℝ) ^ 40 ≤ w ^ 40 := pow_le_pow_left₀ (by norm_num) hw 40
  have h' : (3 : ℝ) ≤ 10 ^ 40 / 4 := by norm_num
  linarith

/-! ### Step 4: the bound on each nontrivial Fourier coefficient -/

theorem norm_prod_le (n : ℕ) [NeZero n] (w : ℝ) (hw : 10 ≤ w)
    (hn_exp : (n : ℝ) = Real.exp (w ^ 10))
    (R : Finset ℕ) (hR : ∀ r ∈ R, r.Prime ∧ ¬ r ∣ n ∧ w ^ 40 / 4 ≤ r ∧ (r : ℝ) ≤ 3 * w ^ 40)
    (hk : w ^ 39 ≤ R.card) (h : ZMod n) (hh : h ≠ 0) :
    ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ≤ 2 ^ R.card / n := by
  have hw0 : 0 < w := by linarith
  have hnpos : (0 : ℝ) < n := by rw [hn_exp]; exact Real.exp_pos _
  set H := h.val with hHdef
  have hH0 : 0 < H := ZMod.val_pos.2 hh
  have hHn : H < n := ZMod.val_lt h
  set t : ℕ → ℤ := fun r => (h * ((r : ZMod n))⁻¹).valMinAbs with htdef
  have hdiv : ∀ r ∈ R, (n : ℤ) ∣ r * t r - H := by
    intro r hr
    have hcop : Nat.Coprime r n := ((hR r hr).1.coprime_iff_not_dvd).2 (hR r hr).2.1
    have h1 : (((r : ℤ) * t r : ℤ) : ZMod n) = ((H : ℤ) : ZMod n) := by
      push_cast
      simp only [htdef, ZMod.coe_valMinAbs, hHdef, ZMod.natCast_zmod_val]
      rw [mul_left_comm, ZMod.coe_mul_inv_eq_one r hcop, mul_one]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).1 h1.symm
  set L : ℝ := w ^ 28 with hLdef
  set B := R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) with hBdef
  set G := R.filter (fun r : ℕ => ¬ |(r : ℝ) * t r| ≤ L * n) with hGdef
  have hBG : B.card + G.card = R.card := Finset.card_filter_add_card_filter_not _
  -- few bad primes
  have hBcard : (B.card : ℝ) ≤ (2 * (L + 1) + 1) * ⌊2 * w ^ 10⌋₊ := by
    have he := ineq_e w hw
    apply card_bad_le n H hH0 hHn R (w ^ 40 / 4) _ _ t hdiv L (by positivity)
    · -- (L + 2) * n < y ^ (m + 1)
      have hL2 : L + 2 ≤ n := by rw [hn_exp, hLdef]; exact ineq_exp w hw
      have h1 : (L + 2) * n ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_right hL2 hnpos.le
      have h2 : (n : ℝ) * n = Real.exp (2 * w ^ 10) := by
        rw [hn_exp, ← Real.exp_add]; ring_nf
      have h3 : Real.exp (2 * w ^ 10) < Real.exp ((⌊2 * w ^ 10⌋₊ + 1 : ℕ) : ℝ) := by
        rw [Real.exp_lt_exp]
        push_cast
        exact Nat.lt_floor_add_one _
      have h4 : Real.exp ((⌊2 * w ^ 10⌋₊ + 1 : ℕ) : ℝ) = Real.exp 1 ^ (⌊2 * w ^ 10⌋₊ + 1) :=
        (Real.exp_one_pow _).symm
      have h5 : Real.exp 1 ^ (⌊2 * w ^ 10⌋₊ + 1) ≤ (w ^ 40 / 4) ^ (⌊2 * w ^ 10⌋₊ + 1) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le he _
      linarith
    · have : (1 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 0
        simp at this
        linarith [Real.add_one_le_exp 1]
      linarith
    · intro r hr
      exact ⟨(hR r hr).1, (hR r hr).2.2.1⟩
  have hBhalf : (B.card : ℝ) ≤ R.card / 2 := by
    have h1 : (⌊2 * w ^ 10⌋₊ : ℝ) ≤ 2 * w ^ 10 := Nat.floor_le (by positivity)
    have h2 : (2 * (L + 1) + 1) * (⌊2 * w ^ 10⌋₊ : ℝ) ≤ (2 * (L + 1) + 1) * (2 * w ^ 10) := by
      apply mul_le_mul_of_nonneg_left h1
      positivity
    have h3 : (2 * (L + 1) + 1) * (2 * w ^ 10) ≤ w ^ 39 / 2 := by
      rw [hLdef]; exact ineq_bad w hw
    linarith
  have hGcard : w ^ 39 / 2 ≤ (G.card : ℝ) := by
    have : (B.card : ℝ) + G.card = R.card := by exact_mod_cast hBG
    linarith
  -- per-factor bounds
  have hfac : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 :=
    fun r _ => norm_one_add_stdAddChar_sq_le _
  set a : ℝ := 4 / (9 * w ^ 24) with hadef
  have hgood : ∀ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 * Real.exp (-a) := by
    intro r hr
    rw [hGdef, Finset.mem_filter] at hr
    obtain ⟨hrR, hrgood⟩ := hr
    push Not at hrgood
    have hr3 : (r : ℝ) ≤ 3 * w ^ 40 := (hR r hrR).2.2.2
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (hR r hrR).1.pos
    have key : (n : ℝ) < 3 * w ^ 12 * |(t r : ℝ)| := by
      rw [abs_mul, abs_of_pos hrpos] at hrgood
      have : w ^ 28 * n < w ^ 28 * (3 * w ^ 12 * |(t r : ℝ)|) := by
        calc w ^ 28 * (n : ℝ) = L * n := by rw [hLdef]
        _ < r * |(t r : ℝ)| := hrgood
        _ ≤ 3 * w ^ 40 * |(t r : ℝ)| := mul_le_mul_of_nonneg_right hr3 (abs_nonneg _)
        _ = w ^ 28 * (3 * w ^ 12 * |(t r : ℝ)|) := by ring
      exact lt_of_mul_lt_mul_left this (by positivity)
    have key2 : 1 / (9 * w ^ 24) ≤ ((t r : ℝ) / n) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (n : ℝ) ^ 2 < (3 * w ^ 12 * |(t r : ℝ)|) ^ 2 :=
        pow_lt_pow_left₀ key hnpos.le (by norm_num)
      calc 1 * (n : ℝ) ^ 2 ≤ (3 * w ^ 12 * |(t r : ℝ)|) ^ 2 := by linarith
      _ = (t r : ℝ) ^ 2 * (9 * w ^ 24) := by rw [mul_pow, mul_pow, sq_abs]; ring
    have hexp : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
    calc ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 := hfac r hrR
    _ ≤ 4 - 16 * (1 / (9 * w ^ 24)) := by linarith
    _ = 4 * (1 - a) := by rw [hadef]; ring
    _ ≤ 4 * Real.exp (-a) := by linarith
  have hbad : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 := by
    intro r hr
    have := hfac r hr
    nlinarith [sq_nonneg ((t r : ℝ) / n)]
  -- the product
  have hprod : ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ^ 2
      ≤ 4 ^ R.card * Real.exp (-(2 * w ^ 10)) := by
    rw [norm_prod, ← Finset.prod_pow,
      ← Finset.prod_filter_mul_prod_filter_not R (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)]
    have hB' : ∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 ^ B.card := by
      calc ∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ ∏ r ∈ B, (4 : ℝ) :=
            Finset.prod_le_prod (fun _ _ => by positivity)
              (fun r hr => hbad r (Finset.mem_filter.1 hr).1)
      _ = 4 ^ B.card := Finset.prod_const _
    have hG' : ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ (4 * Real.exp (-a)) ^ G.card := by
      calc ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
          ≤ ∏ r ∈ G, (4 * Real.exp (-a)) :=
            Finset.prod_le_prod (fun _ _ => by positivity) hgood
      _ = (4 * Real.exp (-a)) ^ G.card := Finset.prod_const _
    have hexpG : Real.exp (-a) ^ G.card ≤ Real.exp (-(2 * w ^ 10)) := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have ha : 0 ≤ a := by positivity
      have : 2 * w ^ 10 ≤ G.card * a := by
        calc 2 * w ^ 10 ≤ (w ^ 39 / 2) * a := by rw [hadef]; exact ineq_good w hw
        _ ≤ G.card * a := mul_le_mul_of_nonneg_right hGcard ha
      linarith
    calc (∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2) *
          ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 ^ B.card * (4 * Real.exp (-a)) ^ G.card :=
          mul_le_mul hB' hG' (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
    _ = 4 ^ R.card * Real.exp (-a) ^ G.card := by
          rw [mul_pow, ← mul_assoc, ← pow_add, hBG]
    _ ≤ 4 ^ R.card * Real.exp (-(2 * w ^ 10)) :=
          mul_le_mul_of_nonneg_left hexpG (by positivity)
  have hfinal : (2 ^ R.card / (n : ℝ)) ^ 2 = 4 ^ R.card * Real.exp (-(2 * w ^ 10)) := by
    have e1 : Real.exp (w ^ 10) ^ 2 = Real.exp (2 * w ^ 10) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hn_exp, div_pow, e1, Real.exp_neg, div_eq_mul_inv, ← pow_mul, mul_comm R.card 2,
      pow_mul]
    norm_num
  rw [← hfinal] at hprod
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hprod

end Lemma1Aux

/-! ### Step 5: Croot's Lemma 1 -/

theorem lemma1 : ∀ᶠ n : ℕ in atTop, ∀ R : Finset ℕ,
    (∀ r ∈ R, r.Prime ∧ ¬ r ∣ n ∧ (Real.log n) ^ 4 / 4 ≤ r ∧ (r : ℝ) ≤ 3 * (Real.log n) ^ 4) →
    (Real.log n) ^ (39 / 10 : ℝ) ≤ R.card →
    ∀ c : ZMod n, ∃ T ⊆ R, ∑ r ∈ T, ((r : ZMod n))⁻¹ = c := by
  have hw : ∀ᶠ n : ℕ in atTop, (10 : ℝ) ≤ (Real.log n) ^ (1 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 10
  filter_upwards [hw, eventually_ge_atTop 2] with n hwn hn2 R hR hk c
  have : NeZero n := ⟨by omega⟩
  set w := (Real.log n) ^ (1 / 10 : ℝ) with hwdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogpos : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlog : Real.log n = w ^ 10 := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hlogpos]
    norm_num
  have hn_exp : (n : ℝ) = Real.exp (w ^ 10) := by
    rw [← hlog, Real.exp_log hnpos]
  have h4 : (Real.log n) ^ 4 = w ^ 40 := by rw [hlog]; ring
  have h39 : (Real.log n) ^ (39 / 10 : ℝ) = w ^ 39 := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hlogpos]
    norm_num
  refine Lemma1Aux.exists_subset_sum_of_norm_prod_le R (fun r => ((r : ZMod n))⁻¹) ?_ c
  intro h hh
  refine Lemma1Aux.norm_prod_le n w hwn hn_exp R ?_ ?_ h hh
  · intro r hr
    obtain ⟨h1, h2, h3, h5⟩ := hR r hr
    rw [h4] at h3 h5
    exact ⟨h1, h2, h3, h5⟩
  · rw [← h39]
    exact hk

end Croot
