import Croot.Basic
import Croot.Primes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The "core" of Croot's Proposition 2 and the far-point lemma (Croot's Lemma 4, modified)

For `n` in the set `G` of pp-smooth rough integers near `X = M^{3/4} (log M)^4` and for each
prime `p ≤ y = ⌊M^{1/5}⌋` we construct `m = n · p^{a-e} · ℓ₁ ℓ₂ k ∈ (M, (1+η)M]` which is
`y`-pp-smooth and divisible by `n` and by `p^{⌊log_p y⌋}`.  The cofactor `m / n` lies in the
small set `cofSet B m`, which bounds how many `n` can produce the same `m`.  The far-point lemma
shows that for `M/2 ≤ |h| ≤ P/2` each core contains an element with no multiple near `h`.
-/

namespace Croot

open Real Finset Filter

/-- Prime powers dividing `m`. -/
def ppDivs (m : ℕ) : Finset ℕ := (Finset.Icc 1 m).filter (fun q => IsPrimePow q ∧ q ∣ m)

/-- The allowed cofactors `q · ℓ₁ · ℓ₂ · k` (with `q ∈ {1} ∪ ppDivs m`, `ℓᵢ ∣ m` prime, `k ≤ B`). -/
def cofSet (B m : ℕ) : Finset ℕ :=
  ((insert 1 (ppDivs m)) ×ˢ (m.primeFactors ×ˢ (m.primeFactors ×ˢ Finset.Icc 1 B))).image
    (fun t => t.1 * t.2.1 * t.2.2.1 * t.2.2.2)

namespace CoreAux

/-! ### Counting helpers -/

/-- `Ω(m) ≤ log₂ m`. -/
lemma sum_factorization_le_log (m : ℕ) (hm : m ≠ 0) :
    ∑ p ∈ m.primeFactors, m.factorization p ≤ Nat.log 2 m := by
  apply Nat.le_log_of_pow_le one_lt_two
  have hprod := Nat.prod_factorization_pow_eq_self hm
  rw [Finsupp.prod, Nat.support_factorization] at hprod
  calc 2 ^ (∑ p ∈ m.primeFactors, m.factorization p)
      = ∏ p ∈ m.primeFactors, 2 ^ m.factorization p := (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
        apply Finset.prod_le_prod'
        intro p hp
        exact Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _
    _ = m := hprod

lemma card_primeFactors_le_log (m : ℕ) : m.primeFactors.card ≤ Nat.log 2 m := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp
  calc m.primeFactors.card = ∑ p ∈ m.primeFactors, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ p ∈ m.primeFactors, m.factorization p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        exact hpp.factorization_pos_of_dvd hpos.ne' (Nat.dvd_of_mem_primeFactors hp)
    _ ≤ Nat.log 2 m := sum_factorization_le_log m hpos.ne'

lemma card_ppDivs_le (m : ℕ) (hm : m ≠ 0) : (ppDivs m).card ≤ Nat.log 2 m := by
  have hsub : ppDivs m ⊆ m.primeFactors.biUnion
      (fun p => (Finset.Icc 1 (m.factorization p)).image (fun j => p ^ j)) := by
    intro q hq
    simp only [ppDivs, Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqm⟩, hpp, hqd⟩ := hq
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    rw [Finset.mem_biUnion]
    refine ⟨p, ?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      exact ⟨hp, (dvd_pow_self p hk.ne').trans hqd, hm⟩
    · rw [Finset.mem_image]
      refine ⟨k, ?_, rfl⟩
      rw [Finset.mem_Icc]
      exact ⟨hk, (hp.pow_dvd_iff_le_factorization hm).1 hqd⟩
  calc (ppDivs m).card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ m.primeFactors, m.factorization p := by
        apply Finset.sum_le_sum
        intro p _
        refine Finset.card_image_le.trans ?_
        simp
    _ ≤ Nat.log 2 m := sum_factorization_le_log m hm

lemma card_cofSet_le (B m : ℕ) (hm : m ≠ 0) :
    (cofSet B m).card ≤ (Nat.log 2 m + 2) ^ 3 * B := by
  unfold cofSet
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_product, Nat.card_Icc,
    Nat.add_sub_cancel]
  have h1 : (insert 1 (ppDivs m)).card ≤ Nat.log 2 m + 2 :=
    (Finset.card_insert_le _ _).trans (by have := card_ppDivs_le m hm; omega)
  have h2 : m.primeFactors.card ≤ Nat.log 2 m + 2 :=
    (card_primeFactors_le_log m).trans (by omega)
  calc (insert 1 (ppDivs m)).card * (m.primeFactors.card * (m.primeFactors.card * B))
      ≤ (Nat.log 2 m + 2) * ((Nat.log 2 m + 2) * ((Nat.log 2 m + 2) * B)) := by
        gcongr
    _ = (Nat.log 2 m + 2) ^ 3 * B := by ring

end CoreAux

/-- Few `n` can give the same `m`. -/
theorem card_fiber_le (B m : ℕ) (hm : 0 < m) (S : Finset ℕ) :
    (S.filter (fun n => n ∣ m ∧ m / n ∈ cofSet B m)).card ≤ (Nat.log 2 m + 2) ^ 3 * B := by
  refine le_trans ?_ (CoreAux.card_cofSet_le B m hm.ne')
  apply Finset.card_le_card_of_injOn (fun n => m / n)
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter] at hn
    exact hn.2.2
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    simp only at hab
    rw [← Nat.div_div_self ha.2.1 hm.ne', ← Nat.div_div_self hb.2.1 hm.ne', hab]

/-- A finite set of positive `y`-pp-smooth integers containing, for every prime `p ≤ y`, a
multiple of `p ^ ⌊log_p y⌋` has least common multiple `lcm(1, …, y)`. -/
theorem lcm_eq_lcmUpto (C : Finset ℕ) (y : ℕ) (hC : ∀ m ∈ C, 0 < m ∧ PPSmooth y m)
    (hfull : ∀ p : ℕ, p.Prime → p ≤ y → ∃ m ∈ C, p ^ Nat.log p y ∣ m) :
    C.lcm id = Nat.lcmUpto y := by
  have h0 : C.lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hx, hx0⟩
    exact (hC x hx).1.ne' hx0
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro m hm
    exact (hC m hm).2.dvd_lcmUpto (hC m hm).1.ne'
  · rw [← Nat.factorization_le_iff_dvd (Nat.lcmUpto_ne_zero y) h0]
    intro p
    by_cases hp : p.Prime
    · rw [Nat.factorization_lcmUpto y hp]
      by_cases hpy : p ≤ y
      · obtain ⟨m, hmC, hdvd⟩ := hfull p hp hpy
        have : p ^ Nat.log p y ∣ C.lcm id := hdvd.trans (Finset.dvd_lcm hmC)
        exact (hp.pow_dvd_iff_le_factorization h0).1 this
      · rw [Nat.log_of_lt (by omega)]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _

/-- Far-point lemma: if all elements of `C` are multiples of `n > 2W` and `W < |h|`,
`|h| + W < lcm C`, then some `m ∈ C` has no multiple within distance `< W` of `h`. -/
theorem exists_far (C : Finset ℕ) (n : ℕ) (W : ℝ) (h : ℤ) (hne : C.Nonempty)
    (_hpos : ∀ m ∈ C, 0 < m) (hdiv : ∀ m ∈ C, n ∣ m) (_hW : 0 ≤ W) (hn : 2 * W < n)
    (hh1 : W < |(h : ℝ)|) (hh2 : |(h : ℝ)| + W < ((C.lcm id : ℕ) : ℝ)) :
    ∃ m ∈ C, ∀ j : ℤ, W ≤ |(h : ℝ) - j * m| := by
  by_contra hcon
  push Not at hcon
  choose! J hJ using hcon
  obtain ⟨m₀, hm₀⟩ := hne
  set z : ℤ := J m₀ * (m₀ : ℤ) with hz
  have hzR : (z : ℝ) = (J m₀ : ℝ) * (m₀ : ℝ) := by rw [hz]; push_cast; ring
  have hz_near : |(h : ℝ) - z| < W := by rw [hzR]; exact hJ m₀ hm₀
  have key : ∀ m ∈ C, J m * (m : ℤ) = z := by
    intro m hm
    have h1 := hJ m hm
    have hdvd : (n : ℤ) ∣ J m * m - z := by
      apply dvd_sub
      · exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (hdiv m hm)) _
      · exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (hdiv m₀ hm₀)) _
    have habs : |J m * (m : ℤ) - z| < n := by
      have hR : |((J m * (m : ℤ) - z : ℤ) : ℝ)| < (n : ℝ) := by
        have e : ((J m * (m : ℤ) - z : ℤ) : ℝ)
            = -(((h : ℝ) - (J m : ℝ) * (m : ℝ)) - ((h : ℝ) - z)) := by
          push_cast; ring
        rw [e, abs_neg]
        calc |((h : ℝ) - (J m : ℝ) * (m : ℝ)) - ((h : ℝ) - z)|
            ≤ |(h : ℝ) - (J m : ℝ) * (m : ℝ)| + |(h : ℝ) - z| := abs_sub _ _
          _ < W + W := add_lt_add h1 hz_near
          _ < n := by linarith
      exact_mod_cast hR
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    linarith
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz_near
    simp at hz_near
    linarith
  have hLdvd : C.lcm id ∣ z.natAbs := by
    apply Finset.lcm_dvd
    intro m hm
    show m ∣ z.natAbs
    exact Int.natCast_dvd.1 ⟨J m, by rw [← key m hm]; ring⟩
  have hle : C.lcm id ≤ z.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hz0) hLdvd
  have hleR : ((C.lcm id : ℕ) : ℝ) ≤ |(z : ℝ)| := by
    have : ((C.lcm id : ℕ) : ℝ) ≤ ((z.natAbs : ℕ) : ℝ) := by exact_mod_cast hle
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  have hzh : |(z : ℝ)| ≤ |(h : ℝ)| + |(h : ℝ) - z| := by
    have := abs_sub_abs_le_abs_sub (z : ℝ) (h : ℝ)
    rw [abs_sub_comm (z : ℝ) (h : ℝ)] at this
    linarith
  linarith

namespace CoreAux

/-! ### Analytic helpers -/

lemma eventually_ten_log_le_sqrt : ∀ᶠ x : ℝ in atTop, 10 * Real.log x ≤ Real.sqrt x := by
  have h := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1 / 2 by norm_num)).bound
    (show (0:ℝ) < 1 / 10 by norm_num)
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hx
  linarith

/-- Supply of primes in `(x, 2.7 x]` avoiding a small exceptional set. -/
lemma exists_prime_avoid : ∃ x₀ : ℝ, 0 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ E : Finset ℕ,
    ((E.card : ℝ)) ^ 2 ≤ x → ∃ ℓ : ℕ, ℓ.Prime ∧ x < ℓ ∧ (ℓ : ℝ) ≤ 27 / 10 * x ∧ ℓ ∉ E := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    ((eventually_card_primes_Ioc_ge.and eventually_ten_log_le_sqrt).and
      (eventually_ge_atTop (2:ℝ)))
  refine ⟨max x₀ 0, le_max_right _ _, fun x hx E hE => ?_⟩
  obtain ⟨⟨hcard, hlog⟩, hx2⟩ := hx₀ x (le_trans (le_max_left _ _) hx)
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hE' : (E.card : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (Nat.cast_nonneg _) (by linarith)).2 hE
  have hlt : (E.card : ℝ) < (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
    have h1 : (E.card : ℝ) * (5 * Real.log x) < x := by
      calc (E.card : ℝ) * (5 * Real.log x) ≤ Real.sqrt x * (Real.sqrt x / 2) :=
            mul_le_mul hE' (by linarith) (by positivity) hs0
        _ = x / 2 := by linear_combination (1 / 2 : ℝ) * hsx
        _ < x := by linarith
    calc (E.card : ℝ) < x / (5 * Real.log x) := by
          rw [lt_div_iff₀ (by positivity)]; exact h1
      _ ≤ _ := hcard
  have hlt' : E.card < ((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card := by
    exact_mod_cast hlt
  obtain ⟨ℓ, hℓP, hℓE⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt'
  rw [Finset.mem_filter, Finset.mem_Ioc] at hℓP
  obtain ⟨⟨h1, h2⟩, hℓ⟩ := hℓP
  refine ⟨ℓ, hℓ, ?_, ?_, hℓE⟩
  · have h3 := Nat.lt_floor_add_one x
    have h1' : (⌊x⌋₊ : ℝ) + 1 ≤ ℓ := by exact_mod_cast Nat.succ_le_of_lt h1
    linarith
  · have h3 := Nat.floor_le (show (0:ℝ) ≤ 27 / 10 * x by linarith)
    have h2' : (ℓ : ℝ) ≤ (⌊(27 / 10 : ℝ) * x⌋₊ : ℝ) := by exact_mod_cast h2
    linarith

lemma eventually_log_pow_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 8 ≤ c * x ^ ((1 : ℝ) / 20) := by
  have h := (isLittleO_log_rpow_rpow_atTop (8 : ℝ) (show (0:ℝ) < 1 / 20 by norm_num)).bound hc
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  have h8 : Real.log x ^ (8 : ℝ) = Real.log x ^ (8 : ℕ) := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h8] at hx
  exact hx

lemma natLog2_le (n : ℕ) (hn : n ≠ 0) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have h2 : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast h1
  have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log n := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have h4 := Real.log_two_gt_d9
  have h5 : (0:ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  nlinarith

lemma exists_k_not_dvd {p : ℕ} (hp : p.Prime) {t η : ℝ} (ht : 0 ≤ t) (hηt : 2 ≤ η * t) :
    ∃ k : ℕ, 1 ≤ k ∧ ¬ p ∣ k ∧ t < k ∧ (k : ℝ) ≤ (1 + η) * t := by
  have h1 := Nat.lt_floor_add_one t
  have h2 := Nat.floor_le ht
  by_cases hdvd : p ∣ ⌊t⌋₊ + 1
  · refine ⟨⌊t⌋₊ + 1 + 1, by omega, ?_, ?_, ?_⟩
    · intro h
      have h' : p ∣ 1 := (Nat.dvd_add_right hdvd).1 h
      exact hp.one_lt.ne' (Nat.dvd_one.1 h')
    · push_cast; linarith
    · push_cast; linarith
  · refine ⟨⌊t⌋₊ + 1, by omega, hdvd, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith

/-! ### Arithmetic helpers -/

lemma ppSmooth_mul_coprime {y a b : ℕ} (hab : Nat.Coprime a b) (ha : PPSmooth y a)
    (hb : PPSmooth y b) : PPSmooth y (a * b) := by
  intro q hq
  rw [Nat.Coprime.primeFactors_mul hab, Finset.mem_union] at hq
  rw [Nat.factorization_mul_apply_of_coprime hab]
  rcases hq with hqa | hqb
  · have hb0 : b.factorization q = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hqb
      exact (Nat.prime_of_mem_primeFactors hqa).one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
          (Nat.dvd_of_mem_primeFactors hqa) hab) hqb)
    rw [hb0, add_zero]; exact ha q hqa
  · have ha0 : a.factorization q = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hqa
      exact (Nat.prime_of_mem_primeFactors hqb).one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hqa hab)
          (Nat.dvd_of_mem_primeFactors hqb))
    rw [ha0, zero_add]; exact hb q hqb

lemma ppSmooth_prime {y ℓ : ℕ} (hℓ : ℓ.Prime) (hℓy : ℓ ≤ y) : PPSmooth y ℓ := by
  intro q hq
  rw [hℓ.primeFactors, Finset.mem_singleton] at hq
  subst hq
  rw [hℓ.factorization_self, pow_one]; exact hℓy

lemma ppSmooth_of_le {y k : ℕ} (hk : k ≤ y) : PPSmooth y k := by
  intro q hq
  exact (Nat.ordProj_le q (Nat.mem_primeFactors.1 hq).2.2).trans hk

lemma ppSmooth_prime_pow {y p a : ℕ} (hp : p.Prime) (hpa : p ^ a ≤ y) : PPSmooth y (p ^ a) := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  have hq' : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).1 (hqp.dvd_of_dvd_pow hqd)
  subst hq'
  rw [hp.factorization_pow, Finsupp.single_eq_same]
  exact hpa

lemma cop_mul {a b c : ℕ} (h1 : Nat.Coprime a c) (h2 : Nat.Coprime b c) :
    Nat.Coprime (a * b) c := Nat.coprime_mul_iff_left.2 ⟨h1, h2⟩

lemma core_arith {B y n p ℓ₁ ℓ₂ k : ℕ} (hn : 0 < n) (hsm : PPSmooth y n)
    (hrough : ∀ q, q.Prime → q ≤ B → ¬ q ∣ n) (hp : p.Prime)
    (hℓ₁ : ℓ₁.Prime) (hℓ₂ : ℓ₂.Prime) (hℓ₁n : ¬ ℓ₁ ∣ n) (hℓ₂n : ¬ ℓ₂ ∣ n)
    (hℓ₁p : ℓ₁ ≠ p) (hℓ₂p : ℓ₂ ≠ p) (hℓ₁₂ : ℓ₁ ≠ ℓ₂) (hℓ₁B : B < ℓ₁) (hℓ₂B : B < ℓ₂)
    (hℓ₁y : ℓ₁ ≤ y) (hℓ₂y : ℓ₂ ≤ y) (hk1 : 1 ≤ k) (hkB : k ≤ B) (hBy : B ≤ y)
    (hpk : ¬ p ∣ k) (hy0 : y ≠ 0) :
    PPSmooth y (n * (p ^ (Nat.log p y - n.factorization p) * ℓ₁ * ℓ₂ * k)) ∧
    n ∣ n * (p ^ (Nat.log p y - n.factorization p) * ℓ₁ * ℓ₂ * k) ∧
    p ^ Nat.log p y ∣ n * (p ^ (Nat.log p y - n.factorization p) * ℓ₁ * ℓ₂ * k) ∧
    n * (p ^ (Nat.log p y - n.factorization p) * ℓ₁ * ℓ₂ * k) / n ∈
      cofSet B (n * (p ^ (Nat.log p y - n.factorization p) * ℓ₁ * ℓ₂ * k)) := by
  set a := Nat.log p y with ha
  set e := n.factorization p with he
  have hea : e ≤ a := by
    by_cases hpn : p ∣ n
    · exact Nat.le_log_of_pow_le hp.one_lt (hsm p (Nat.mem_primeFactors.2 ⟨hp, hpn, hn.ne'⟩))
    · rw [he, Nat.factorization_eq_zero_of_not_dvd hpn]; exact Nat.zero_le _
  set m := n * (p ^ (a - e) * ℓ₁ * ℓ₂ * k) with hm
  have hk0 : k ≠ 0 := by omega
  have hm0 : m ≠ 0 := by
    rw [hm]
    apply Nat.mul_ne_zero hn.ne'
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero)
      hℓ₁.ne_zero) hℓ₂.ne_zero) hk0
  set n' := n / p ^ e with hn'
  have hn_eq : p ^ e * n' = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hn'dvd : n' ∣ n := Nat.ordCompl_dvd n p
  have hm_eq : m = p ^ a * n' * ℓ₁ * ℓ₂ * k := by
    calc m = (p ^ e * n') * (p ^ (a - e) * ℓ₁ * ℓ₂ * k) := by rw [hm, hn_eq]
      _ = p ^ (e + (a - e)) * n' * ℓ₁ * ℓ₂ * k := by rw [pow_add]; ring
      _ = p ^ a * n' * ℓ₁ * ℓ₂ * k := by rw [Nat.add_sub_cancel' hea]
  -- coprimality facts
  have hc_p_ℓ₁ : Nat.Coprime p ℓ₁ := (Nat.coprime_primes hp hℓ₁).2 (Ne.symm hℓ₁p)
  have hc_p_ℓ₂ : Nat.Coprime p ℓ₂ := (Nat.coprime_primes hp hℓ₂).2 (Ne.symm hℓ₂p)
  have hc_ℓ₁_ℓ₂ : Nat.Coprime ℓ₁ ℓ₂ := (Nat.coprime_primes hℓ₁ hℓ₂).2 hℓ₁₂
  have hc_p_n' : Nat.Coprime p n' := Nat.coprime_ordCompl hp hn.ne'
  have hc_n'_ℓ₁ : Nat.Coprime n' ℓ₁ := Nat.Coprime.symm
    ((Nat.Prime.coprime_iff_not_dvd hℓ₁).2 (fun h => hℓ₁n (h.trans hn'dvd)))
  have hc_n'_ℓ₂ : Nat.Coprime n' ℓ₂ := Nat.Coprime.symm
    ((Nat.Prime.coprime_iff_not_dvd hℓ₂).2 (fun h => hℓ₂n (h.trans hn'dvd)))
  have hc_p_k : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd hp).2 hpk
  have hc_ℓ₁_k : Nat.Coprime ℓ₁ k := (Nat.Prime.coprime_iff_not_dvd hℓ₁).2 (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)
  have hc_ℓ₂_k : Nat.Coprime ℓ₂ k := (Nat.Prime.coprime_iff_not_dvd hℓ₂).2 (fun h => by
    have := Nat.le_of_dvd (by omega) h; omega)
  have hc_n'_k : Nat.Coprime n' k := Nat.coprime_of_dvd (fun q hq hqn' hqk => by
    have hqB : q ≤ B := (Nat.le_of_dvd (by omega) hqk).trans hkB
    exact hrough q hq hqB (hqn'.trans hn'dvd))
  -- smoothness
  have hsm_m : PPSmooth y m := by
    rw [hm_eq]
    have hpa : p ^ a ≤ y := Nat.pow_log_le_self p hy0
    refine ppSmooth_mul_coprime ?_ ?_ (ppSmooth_of_le (hkB.trans hBy))
    · exact cop_mul (cop_mul (cop_mul (Nat.Coprime.pow_left a hc_p_k) hc_n'_k) hc_ℓ₁_k) hc_ℓ₂_k
    refine ppSmooth_mul_coprime ?_ ?_ (ppSmooth_prime hℓ₂ hℓ₂y)
    · exact cop_mul (cop_mul (Nat.Coprime.pow_left a hc_p_ℓ₂) hc_n'_ℓ₂) hc_ℓ₁_ℓ₂
    refine ppSmooth_mul_coprime ?_ ?_ (ppSmooth_prime hℓ₁ hℓ₁y)
    · exact cop_mul (Nat.Coprime.pow_left a hc_p_ℓ₁) hc_n'_ℓ₁
    exact ppSmooth_mul_coprime (Nat.Coprime.pow_left a hc_p_n') (ppSmooth_prime_pow hp hpa)
      (hsm.of_dvd hn.ne' hn'dvd)
  have hdiv : m / n = p ^ (a - e) * ℓ₁ * ℓ₂ * k := by
    rw [hm]; exact Nat.mul_div_cancel_left _ hn
  have hmem : p ^ (a - e) * ℓ₁ * ℓ₂ * k ∈ cofSet B m := by
    unfold cofSet
    rw [Finset.mem_image]
    refine ⟨(p ^ (a - e), ℓ₁, ℓ₂, k), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_Icc]
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases hae : a - e = 0
      · left; rw [hae, pow_zero]
      · right
        unfold ppDivs
        rw [Finset.mem_filter, Finset.mem_Icc]
        have hd : p ^ (a - e) ∣ m := Dvd.intro (n * ℓ₁ * ℓ₂ * k) (by rw [hm]; ring)
        exact ⟨⟨Nat.one_le_pow _ _ hp.pos, Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd⟩,
          hp.isPrimePow.pow hae, hd⟩
    · exact Nat.mem_primeFactors.2
        ⟨hℓ₁, Dvd.intro (n * p ^ (a - e) * ℓ₂ * k) (by rw [hm]; ring), hm0⟩
    · exact Nat.mem_primeFactors.2
        ⟨hℓ₂, Dvd.intro (n * p ^ (a - e) * ℓ₁ * k) (by rw [hm]; ring), hm0⟩
    · exact ⟨hk1, hkB⟩
  refine ⟨hsm_m, ⟨_, hm⟩, ?_, ?_⟩
  · rw [hm_eq]; exact Dvd.intro (n' * ℓ₁ * ℓ₂ * k) (by ring)
  · rw [hdiv]; exact hmem

lemma core_W_bounds {u L D W : ℝ} (hu0 : 0 < u) (hL1 : 1 ≤ L) (hD_lo : u ^ 30 * L ^ 4 < D)
    (hD_hi : D ≤ 2 * L ^ 4 * u ^ 38) (hWD : W * D = u ^ 40) (hWpos : 0 < W) :
    u ^ 2 ≤ 2 * L ^ 4 * W ∧ W < u ^ 10 := by
  constructor
  · have h1 : u ^ 2 * u ^ 38 ≤ (2 * L ^ 4 * W) * u ^ 38 := by
      calc u ^ 2 * u ^ 38 = W * D := by rw [hWD]; ring
        _ ≤ W * (2 * L ^ 4 * u ^ 38) := mul_le_mul_of_nonneg_left hD_hi hWpos.le
        _ = (2 * L ^ 4 * W) * u ^ 38 := by ring
    exact le_of_mul_le_mul_right h1 (by positivity)
  · have h1 : (W * L ^ 4) * u ^ 30 < u ^ 10 * u ^ 30 := by
      calc (W * L ^ 4) * u ^ 30 = W * (u ^ 30 * L ^ 4) := by ring
        _ < W * D := mul_lt_mul_of_pos_left hD_lo hWpos
        _ = u ^ 10 * u ^ 30 := by rw [hWD]; ring
    have h2 : W * L ^ 4 < u ^ 10 := lt_of_mul_lt_mul_right h1 (by positivity)
    have h3 : W ≤ W * L ^ 4 := le_mul_of_one_le_right hWpos.le (one_le_pow₀ hL1)
    linarith

lemma core_s_bounds {η x₀ b u L W s : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hx₀ : 0 ≤ x₀)
    (hb : 0 ≤ b) (hu0 : 0 < u) (hL1 : 1 ≤ L)
    (hC : 117 * (x₀ + b + 16) ^ 2 * L ^ 8 ≤ η * u ^ 2)
    (hW_lo : u ^ 2 ≤ 2 * L ^ 4 * W) (hW_hi : W < u ^ 10) (hWpos : 0 < W)
    (hs_pos : 0 < s) (hsV : s * s = η * W / 8) :
    27 / 10 * (x₀ + b + 16 * L ^ 2) ≤ s ∧ s ≤ u ^ 5 := by
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hK0 : 0 ≤ x₀ + b + 16 * L ^ 2 := by positivity
  have hK_le : x₀ + b + 16 * L ^ 2 ≤ (x₀ + b + 16) * L ^ 2 := by
    nlinarith [mul_nonneg hx₀ (sub_nonneg.2 hL2), mul_nonneg hb (sub_nonneg.2 hL2)]
  constructor
  · have h1 : η * u ^ 2 ≤ 16 * L ^ 4 * (s * s) := by
      rw [hsV]; nlinarith [mul_le_mul_of_nonneg_left hW_lo hη.le]
    have h2 : (x₀ + b + 16 * L ^ 2) ^ 2 ≤ ((x₀ + b + 16) * L ^ 2) ^ 2 :=
      pow_le_pow_left₀ hK0 hK_le 2
    have h3 : (27 / 10 * (x₀ + b + 16 * L ^ 2)) ^ 2 * (16 * L ^ 4) ≤ s ^ 2 * (16 * L ^ 4) := by
      calc (27 / 10 * (x₀ + b + 16 * L ^ 2)) ^ 2 * (16 * L ^ 4)
          = 11664 / 100 * (x₀ + b + 16 * L ^ 2) ^ 2 * L ^ 4 := by ring
        _ ≤ 11664 / 100 * ((x₀ + b + 16) * L ^ 2) ^ 2 * L ^ 4 := by gcongr
        _ = 11664 / 100 * (x₀ + b + 16) ^ 2 * L ^ 8 := by ring
        _ ≤ 117 * (x₀ + b + 16) ^ 2 * L ^ 8 := by gcongr; norm_num
        _ ≤ η * u ^ 2 := hC
        _ ≤ 16 * L ^ 4 * (s * s) := h1
        _ = s ^ 2 * (16 * L ^ 4) := by ring
    exact le_of_pow_le_pow_left₀ two_ne_zero hs_pos.le
      (le_of_mul_le_mul_right h3 (by positivity))
  · have h1 : s ^ 2 ≤ (u ^ 5) ^ 2 := by
      have : η * W ≤ W := by nlinarith
      nlinarith [hW_hi]
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h1

lemma core_n_le_M {η x₀ b u L : ℝ} {n M : ℕ} (hη1 : η ≤ 1) (hx₀ : 0 ≤ x₀) (hb : 0 ≤ b)
    (hu1 : 1 ≤ u) (hL1 : 1 ≤ L) (hC : 117 * (x₀ + b + 16) ^ 2 * L ^ 8 ≤ η * u ^ 2)
    (hn2 : (n : ℝ) ≤ 2 * (u ^ 30 * L ^ 4)) (hM : (M : ℝ) = u ^ 40) : n ≤ M := by
  have h2L : 2 * L ^ 4 ≤ u ^ 10 := by
    have h16 : (16:ℝ) ^ 2 ≤ (x₀ + b + 16) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hL8 : L ^ 4 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
    have hu2 : u ^ 2 ≤ u ^ 10 := pow_le_pow_right₀ hu1 (by norm_num)
    have hL8' : 0 ≤ L ^ 8 := by positivity
    have h3 : (16:ℝ) ^ 2 * L ^ 8 ≤ (x₀ + b + 16) ^ 2 * L ^ 8 :=
      mul_le_mul_of_nonneg_right h16 hL8'
    have hηu : η * u ^ 2 ≤ u ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hη1) (sq_nonneg u)]
    linarith
  have : (n : ℝ) ≤ M := by
    rw [hM]
    calc (n:ℝ) ≤ 2 * (u ^ 30 * L ^ 4) := hn2
      _ = (2 * L ^ 4) * u ^ 30 := by ring
      _ ≤ u ^ 10 * u ^ 30 := by gcongr
      _ = u ^ 40 := by ring
  exact_mod_cast this

lemma card_pf_sq_le {n M : ℕ} {L : ℝ} (hn0 : 0 < n) (hnM : n ≤ M) (hLM : Real.log M ≤ L)
    (hL1 : 1 ≤ L) : (((n.primeFactors.card + 2 : ℕ) : ℝ)) ^ 2 ≤ 16 * L ^ 2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have h1 := natLog2_le n hn0.ne'
  have h2 : Real.log n ≤ Real.log M := Real.log_le_log hnR (by exact_mod_cast hnM)
  have h3 : (n.primeFactors.card : ℝ) ≤ Nat.log 2 n := by
    exact_mod_cast card_primeFactors_le_log n
  have h4 : (((n.primeFactors.card + 2 : ℕ) : ℝ)) ≤ 4 * L := by push_cast; linarith
  calc (((n.primeFactors.card + 2 : ℕ) : ℝ)) ^ 2 ≤ (4 * L) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h4 2
    _ = 16 * L ^ 2 := by ring

/-- Choice of the two auxiliary primes `ℓ₁ ∈ (10s/27, s]` and `ℓ₂ ∈ (s²/ℓ₁, 2.7 s²/ℓ₁]`. -/
lemma core_two_primes {x₀ s : ℝ}
    (hprime : ∀ x : ℝ, x₀ ≤ x → ∀ E : Finset ℕ, ((E.card : ℝ)) ^ 2 ≤ x →
      ∃ ℓ : ℕ, ℓ.Prime ∧ x < ℓ ∧ (ℓ : ℝ) ≤ 27 / 10 * x ∧ ℓ ∉ E)
    (hs_pos : 0 < s) {n : ℕ} (hn0 : 0 < n) (p : ℕ) (hx₀ : x₀ ≤ 10 * s / 27)
    (hcard : (((n.primeFactors.card + 2 : ℕ) : ℝ)) ^ 2 ≤ 10 * s / 27) :
    ∃ ℓ₁ ℓ₂ : ℕ, ℓ₁.Prime ∧ ℓ₂.Prime ∧ ¬ ℓ₁ ∣ n ∧ ¬ ℓ₂ ∣ n ∧ ℓ₁ ≠ p ∧ ℓ₂ ≠ p ∧ ℓ₁ ≠ ℓ₂ ∧
      10 * s / 27 < ℓ₁ ∧ 10 * s / 27 < ℓ₂ ∧ (ℓ₁ : ℝ) ≤ s ∧ (ℓ₂ : ℝ) ≤ 729 / 100 * s ∧
      s * s < (ℓ₁ : ℝ) * ℓ₂ ∧ (ℓ₁ : ℝ) * ℓ₂ ≤ 27 / 10 * (s * s) := by
  have hcardE : ∀ E : Finset ℕ, E.card ≤ n.primeFactors.card + 2 → ∀ x : ℝ,
      10 * s / 27 ≤ x → ((E.card : ℝ)) ^ 2 ≤ x := by
    intro E hE x hx
    have h1 : (E.card : ℝ) ≤ ((n.primeFactors.card + 2 : ℕ) : ℝ) := by exact_mod_cast hE
    calc (E.card : ℝ) ^ 2 ≤ (((n.primeFactors.card + 2 : ℕ) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
      _ ≤ 10 * s / 27 := hcard
      _ ≤ x := hx
  obtain ⟨ℓ₁, hℓ₁, hℓ₁x, hℓ₁s, hℓ₁E⟩ := hprime (10 * s / 27) hx₀ (insert p n.primeFactors)
    (hcardE _ ((Finset.card_insert_le _ _).trans (by omega)) _ le_rfl)
  rw [Finset.mem_insert, not_or] at hℓ₁E
  obtain ⟨hℓ₁p, hℓ₁n⟩ := hℓ₁E
  have hℓ₁R : (ℓ₁ : ℝ) ≤ s := by linarith
  have hℓ₁pos : (0:ℝ) < ℓ₁ := by exact_mod_cast hℓ₁.pos
  have hsx₂ : s ≤ s * s / ℓ₁ := by
    rw [le_div_iff₀ hℓ₁pos]
    exact mul_le_mul_of_nonneg_left hℓ₁R hs_pos.le
  have hx₁x₂ : 10 * s / 27 ≤ s * s / ℓ₁ := le_trans (by linarith) hsx₂
  obtain ⟨ℓ₂, hℓ₂, hℓ₂x, hℓ₂le, hℓ₂E⟩ := hprime (s * s / ℓ₁) (hx₀.trans hx₁x₂)
    (insert ℓ₁ (insert p n.primeFactors))
    (hcardE _ (by
      have h1 := Finset.card_insert_le ℓ₁ (insert p n.primeFactors)
      have h2 := Finset.card_insert_le p n.primeFactors
      omega) _ hx₁x₂)
  rw [Finset.mem_insert, Finset.mem_insert, not_or, not_or] at hℓ₂E
  obtain ⟨hℓ₂ℓ₁, hℓ₂p, hℓ₂n⟩ := hℓ₂E
  have hℓ₁ne : (ℓ₁ : ℝ) ≠ 0 := hℓ₁pos.ne'
  refine ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, fun h => hℓ₁n (Nat.mem_primeFactors.2 ⟨hℓ₁, h, hn0.ne'⟩),
    fun h => hℓ₂n (Nat.mem_primeFactors.2 ⟨hℓ₂, h, hn0.ne'⟩), hℓ₁p, hℓ₂p, Ne.symm hℓ₂ℓ₁,
    hℓ₁x, lt_of_le_of_lt hx₁x₂ hℓ₂x, hℓ₁R, ?_, ?_, ?_⟩
  · have h1 : s * s / ℓ₁ ≤ s * s / (10 * s / 27) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hℓ₁x.le
    have h2 : s * s / (10 * s / 27) = 27 / 10 * s := by field_simp
    calc (ℓ₂ : ℝ) ≤ 27 / 10 * (s * s / ℓ₁) := hℓ₂le
      _ ≤ 27 / 10 * (s * s / (10 * s / 27)) := by gcongr
      _ = 729 / 100 * s := by rw [h2]; ring
  · have h1 := hℓ₂x
    rw [div_lt_iff₀ hℓ₁pos] at h1
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hℓ₂le hℓ₁pos.le
    calc (ℓ₁ : ℝ) * ℓ₂ ≤ ℓ₁ * (27 / 10 * (s * s / ℓ₁)) := h1
      _ = 27 / 10 * (s * s) := by field_simp

/-- The deterministic construction behind `core_exists`, with all "`M` large" facts as
hypotheses. Here `u = M^{1/40}`, `L = log M`, `y = ⌊u^8⌋`. -/
lemma core_det {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hprime : ∀ x : ℝ, x₀ ≤ x → ∀ E : Finset ℕ, ((E.card : ℝ)) ^ 2 ≤ x →
      ∃ ℓ : ℕ, ℓ.Prime ∧ x < ℓ ∧ (ℓ : ℝ) ≤ 27 / 10 * x ∧ ℓ ∉ E)
    {B y M : ℕ} {u L : ℝ} (hB : 16 / η ≤ B) (hBy : B ≤ y)
    (hy1 : (y : ℝ) ≤ u ^ 8) (hy2 : ∀ ℓ : ℕ, (ℓ : ℝ) ≤ u ^ 8 → ℓ ≤ y)
    (hM : (M : ℝ) = u ^ 40) (hu : 2 ≤ u) (hL1 : 1 ≤ L) (hLM : Real.log M ≤ L)
    (hC : 117 * (x₀ + B + 16) ^ 2 * L ^ 8 ≤ η * u ^ 2)
    {n : ℕ} (hn1 : u ^ 30 * L ^ 4 < n) (hn2 : (n : ℝ) ≤ 2 * (u ^ 30 * L ^ 4))
    (hsm : PPSmooth y n) (hrough : ∀ q, q.Prime → q ≤ B → ¬ q ∣ n)
    {p : ℕ} (hp : p.Prime) (hpy : p ≤ y) :
    ∃ m : ℕ, M < m ∧ (m : ℝ) ≤ (1 + η) * M ∧ PPSmooth y m ∧
      n ∣ m ∧ p ^ Nat.log p y ∣ m ∧ m / n ∈ cofSet B m := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hB0 : (0:ℝ) ≤ B := Nat.cast_nonneg B
  have hnR : (0:ℝ) < n := lt_of_le_of_lt (by positivity) hn1
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hy0 : y ≠ 0 := by have := hp.two_le; omega
  -- the cofactor `r = p ^ (a - e)`
  set r := p ^ (Nat.log p y - n.factorization p) with hr
  have hr1R : (1:ℝ) ≤ r := by exact_mod_cast Nat.one_le_pow _ _ hp.pos
  have hry : r ≤ y :=
    le_trans (Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)) (Nat.pow_log_le_self p hy0)
  have hryR : (r:ℝ) ≤ u ^ 8 := le_trans (by exact_mod_cast hry) hy1
  -- `D = n r` and `W = M / D`
  set D : ℝ := (n : ℝ) * r with hD
  have hDpos : 0 < D := by positivity
  have hD_lo : u ^ 30 * L ^ 4 < D := by
    calc u ^ 30 * L ^ 4 < n := hn1
      _ = n * 1 := (mul_one _).symm
      _ ≤ D := mul_le_mul_of_nonneg_left hr1R hnR.le
  have hD_hi : D ≤ 2 * L ^ 4 * u ^ 38 := by
    calc D = n * r := rfl
      _ ≤ (2 * (u ^ 30 * L ^ 4)) * u ^ 8 := mul_le_mul hn2 hryR (by positivity) (by positivity)
      _ = 2 * L ^ 4 * u ^ 38 := by ring
  set W : ℝ := (M : ℝ) / D with hW
  have hWD : W * D = u ^ 40 := by rw [hW, div_mul_cancel₀ _ hDpos.ne', hM]
  have hWpos : 0 < W := by rw [hW, hM]; positivity
  obtain ⟨hW_lo, hW_hi⟩ := core_W_bounds hu0 hL1 hD_lo hD_hi hWD hWpos
  -- `s = √(ηW/8)`
  obtain ⟨s, hs_pos, hsV⟩ : ∃ s : ℝ, 0 < s ∧ s * s = η * W / 8 :=
    ⟨Real.sqrt (η * W / 8), Real.sqrt_pos.2 (by positivity), Real.mul_self_sqrt (by positivity)⟩
  obtain ⟨hs_lo, hs_hi⟩ :=
    core_s_bounds hη hη1 hx₀ hB0 hu0 hL1 hC hW_lo hW_hi hWpos hs_pos hsV
  have hL2 : 0 ≤ L ^ 2 := by positivity
  have hnM : n ≤ M := core_n_le_M hη1 hx₀ hB0 hu1 hL1 hC hn2 hM
  have hcard := card_pf_sq_le hn0 hnM hLM hL1
  -- the two primes
  obtain ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, hℓ₁n, hℓ₂n, hℓ₁p, hℓ₂p, hℓ₁₂, hℓ₁x, hℓ₂x, hℓ₁R, hℓ₂R, hP_lo,
    hP_hi⟩ := core_two_primes hprime hs_pos hn0 p (by linarith only [hs_lo, hB0, hL2])
      (by linarith only [hs_lo, hB0, hx₀, hcard])
  -- the integer `k`
  set P : ℝ := (ℓ₁ : ℝ) * ℓ₂ with hP
  have hPpos : 0 < P := lt_trans (mul_pos hs_pos hs_pos) hP_lo
  have hηW : η * W = 8 * (s * s) := by rw [hsV]; ring
  have hηt : 2 ≤ η * (W / P) := by
    rw [← mul_div_assoc, le_div_iff₀ hPpos, hηW]
    nlinarith only [hP_hi, mul_pos hs_pos hs_pos]
  have ht_hi : W / P < 8 / η := by
    rw [div_lt_div_iff₀ hPpos hη]
    nlinarith only [hP_lo, hηW]
  have ht0 : 0 ≤ W / P := by positivity
  obtain ⟨k, hk1, hpk, htk, hk_hi⟩ := exists_k_not_dvd hp ht0 hηt
  have hkB : k ≤ B := by
    have h1 : (k : ℝ) ≤ B := by
      have h2 : (1 + η) * (W / P) ≤ 2 * (W / P) := by
        nlinarith only [mul_le_mul_of_nonneg_right hη1 ht0]
      calc (k : ℝ) ≤ (1 + η) * (W / P) := hk_hi
        _ ≤ 2 * (W / P) := h2
        _ ≤ 2 * (8 / η) := by linarith only [ht_hi]
        _ = 16 / η := by ring
        _ ≤ B := hB
    exact_mod_cast h1
  have hBx₁ : (B : ℝ) ≤ 10 * s / 27 := by linarith only [hs_lo, hx₀, hL2]
  have hℓ₁B : B < ℓ₁ := by exact_mod_cast lt_of_le_of_lt hBx₁ hℓ₁x
  have hℓ₂B : B < ℓ₂ := by exact_mod_cast lt_of_le_of_lt hBx₁ hℓ₂x
  have hu58 : u ^ 5 ≤ u ^ 8 := pow_le_pow_right₀ hu1 (by norm_num)
  have hℓ₁y : ℓ₁ ≤ y := hy2 ℓ₁ (by linarith only [hℓ₁R, hs_hi, hu58])
  have hℓ₂y : ℓ₂ ≤ y := hy2 ℓ₂ (by
    have hu3 : (8:ℝ) ≤ u ^ 3 := by
      calc (8:ℝ) = 2 ^ 3 := by norm_num
        _ ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    calc (ℓ₂ : ℝ) ≤ 729 / 100 * s := hℓ₂R
      _ ≤ 729 / 100 * u ^ 5 := by gcongr
      _ ≤ u ^ 3 * u ^ 5 := by gcongr; linarith only [hu3]
      _ = u ^ 8 := by ring)
  obtain ⟨hsm', hdvd1, hdvd2, hcof⟩ := core_arith hn0 hsm hrough hp hℓ₁ hℓ₂ hℓ₁n hℓ₂n
    hℓ₁p hℓ₂p hℓ₁₂ hℓ₁B hℓ₂B hℓ₁y hℓ₂y hk1 hkB hBy hpk hy0
  have hmR : ((n * (r * ℓ₁ * ℓ₂ * k) : ℕ) : ℝ) = D * (P * k) := by
    rw [hD, hP]; push_cast; ring
  have hPt : P * (W / P) = W := by field_simp
  refine ⟨n * (r * ℓ₁ * ℓ₂ * k), ?_, ?_, hsm', hdvd1, hdvd2, hcof⟩
  · have h1 : (M : ℝ) < ((n * (r * ℓ₁ * ℓ₂ * k) : ℕ) : ℝ) := by
      rw [hmR]
      calc (M : ℝ) = D * (P * (W / P)) := by rw [hPt, hM, ← hWD]; ring
        _ < D * (P * k) := by gcongr
    exact_mod_cast h1
  · rw [hmR]
    calc D * (P * k) ≤ D * (P * ((1 + η) * (W / P))) := by gcongr
      _ = (1 + η) * (D * (P * (W / P))) := by ring
      _ = (1 + η) * (W * D) := by rw [hPt]; ring
      _ = (1 + η) * M := by rw [hWD, hM]

end CoreAux

/-- Construction of the core elements. -/
theorem core_exists (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∀ᶠ M : ℕ in atTop,
    ∀ n : ℕ, (M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4 < n →
      (n : ℝ) ≤ 2 * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4) →
      PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ n → (∀ p ∈ Finset.Iic ⌈16 / η⌉₊, p.Prime → ¬ p ∣ n) →
      ∀ p : ℕ, p.Prime → p ≤ ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ →
        ∃ m : ℕ, M < m ∧ (m : ℝ) ≤ (1 + η) * M ∧ PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ m ∧
          n ∣ m ∧ p ^ Nat.log p ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ ∣ m ∧ m / n ∈ cofSet ⌈16 / η⌉₊ m := by
  obtain ⟨x₀, hx₀, hprime⟩ := CoreAux.exists_prime_avoid
  set B := ⌈16 / η⌉₊ with hBdef
  have hB : 16 / η ≤ (B : ℝ) := Nat.le_ceil _
  have hK0 : 0 < 117 * (x₀ + (B : ℝ) + 16) ^ 2 := by positivity
  have hev1 := CoreAux.eventually_log_pow_le (η / (117 * (x₀ + (B : ℝ) + 16) ^ 2))
    (div_pos hη hK0)
  have hev2 : ∀ᶠ x : ℝ in atTop, max 2 (B : ℝ) ≤ x ^ ((1 : ℝ) / 40) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop _
  have hev3 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (hev1.and (hev2.and hev3))] with M hM
  obtain ⟨h1, h2, h3⟩ := hM
  intro n hn1 hn2 hsm hrough p hp hpy
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  set u : ℝ := (M : ℝ) ^ ((1 : ℝ) / 40) with hu
  have hpow : ∀ k : ℕ, (M : ℝ) ^ ((1 : ℝ) / 40 * (k : ℝ)) = u ^ k :=
    fun k => Real.rpow_mul_natCast hM0 _ _
  have e30 : (M : ℝ) ^ (3 / 4 : ℝ) = u ^ 30 := by rw [← hpow 30]; norm_num
  have e8 : (M : ℝ) ^ (1 / 5 : ℝ) = u ^ 8 := by rw [← hpow 8]; norm_num
  have e2 : (M : ℝ) ^ ((1 : ℝ) / 20) = u ^ 2 := by rw [← hpow 2]; norm_num
  have e40 : (M : ℝ) = u ^ 40 := by rw [← hpow 40]; norm_num
  rw [e30] at hn1 hn2
  rw [e8] at hsm hpy ⊢
  rw [e2] at h1
  have hu2 : 2 ≤ u := le_trans (le_max_left _ _) h2
  have huB : (B : ℝ) ≤ u := le_trans (le_max_right _ _) h2
  have hu1 : 1 ≤ u := by linarith
  have hC : 117 * (x₀ + B + 16) ^ 2 * Real.log M ^ 8 ≤ η * u ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1 hK0.le
    calc 117 * (x₀ + B + 16) ^ 2 * Real.log M ^ 8
        = 117 * (x₀ + B + 16) ^ 2 * (Real.log M ^ 8) := by ring
      _ ≤ 117 * (x₀ + B + 16) ^ 2 * (η / (117 * (x₀ + B + 16) ^ 2) * u ^ 2) := this
      _ = η * u ^ 2 := by field_simp
  have hu8 : u ≤ u ^ 8 := by
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ 8 := pow_le_pow_right₀ hu1 (by norm_num)
  have hBy : B ≤ ⌊u ^ 8⌋₊ := Nat.le_floor (by linarith)
  exact CoreAux.core_det hη hη1 hx₀ hprime hB hBy (Nat.floor_le (by positivity))
    (fun ℓ hℓ => Nat.le_floor hℓ) e40 hu2 h3 le_rfl hC hn1 hn2 hsm
    (fun q hq hqB => hrough q (Finset.mem_Iic.2 hqB) hq) hp hpy

end Croot
