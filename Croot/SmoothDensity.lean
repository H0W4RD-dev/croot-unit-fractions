import Croot.Basic
import Croot.Primes

/-!
# Positive density of prime-power-smooth numbers in the ranges needed for Proposition 2

With `y = ⌊M^{1/5}⌋`:
* `y`-pp-smooth, `B`-rough integers have positive density in `(X, 2X]`,
  `X = M^{3/4} (log M)^4`;
* `y`-pp-smooth integers in `(M, (1+η) M]` have reciprocal mass `≫ η`.

Construction: products `p₁ ⋯ p_r · t` with the `pᵢ` taken from disjoint ranges of primes
inside `(y^α, y^β]` and a free cofactor `t < y^α` (so the factorization is unique);
Chebyshev bounds give `∑_{p ∈ range} 1/p ≫ 1`.
-/

namespace Croot

open Real Finset Filter

/-! ## Prime-power-smooth helpers -/

private lemma ppSmooth_of_le {y n : ℕ} (hn : n ≠ 0) (h : n ≤ y) : PPSmooth y n :=
  fun p _ => (Nat.ordProj_le p hn).trans h

private lemma PPSmooth.mul_coprime {y a b : ℕ} (ha : PPSmooth y a) (hb : PPSmooth y b) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hab : Nat.Coprime a b) : PPSmooth y (a * b) :=
  ppSmooth_of_dvd_lcmUpto
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd hab (ha.dvd_lcmUpto ha0) (hb.dvd_lcmUpto hb0))

private lemma natCast_sub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

/-! ## Reciprocal sums of primes over long ranges -/

/-- Over `(x, 2.7^K x]` the primes have reciprocal sum `≥ K / (14 L)` whenever
`log (2.7^K x) ≤ L` (Chebyshev, one block `(z, 2.7 z]` at a time). -/
private lemma exists_block_bound : ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ K : ℕ, ∀ L : ℝ, 0 < L →
    Real.log ((27 / 10 : ℝ) ^ K * x) ≤ L →
    (K : ℝ) / (14 * L) ≤
      ∑ p ∈ Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) ^ K * x⌋₊, (if p.Prime then (1 : ℝ) / p else 0) := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp eventually_card_primes_Ioc_ge
  refine ⟨max X₁ 2, le_max_right _ _, fun x hx K => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxX : X₁ ≤ x := le_trans (le_max_left _ _) hx
  induction K with
  | zero =>
    intro L _ _
    simp
  | succ K ih =>
    intro L hL hlog
    have hcK : (1 : ℝ) ≤ (27 / 10 : ℝ) ^ K := one_le_pow₀ (by norm_num)
    have hz_eq : (27 / 10 : ℝ) ^ (K + 1) * x = (27 / 10 : ℝ) * ((27 / 10 : ℝ) ^ K * x) := by
      rw [pow_succ]; ring
    rw [hz_eq] at hlog ⊢
    generalize hz : (27 / 10 : ℝ) ^ K * x = z at ih hlog ⊢
    have hz2 : x ≤ z := by rw [← hz]; nlinarith
    have hzX : X₁ ≤ z := le_trans hxX hz2
    have hz0 : 0 < z := by linarith
    have hlogz : Real.log z ≤ L := le_trans (Real.log_le_log hz0 (by linarith)) hlog
    have h1 := ih L hL hlogz
    have hfl : ⌊x⌋₊ ≤ ⌊z⌋₊ := Nat.floor_le_floor hz2
    have hfl2 : ⌊z⌋₊ ≤ ⌊(27 / 10 : ℝ) * z⌋₊ := Nat.floor_le_floor (by linarith)
    rw [← Finset.sum_Ioc_consecutive _ hfl hfl2]
    have hblock : 1 / (14 * L) ≤
        ∑ p ∈ Ioc ⌊z⌋₊ ⌊(27 / 10 : ℝ) * z⌋₊, (if p.Prime then (1 : ℝ) / p else 0) := by
      rw [← Finset.sum_filter]
      have hcnt := hX₁ z hzX
      have hlz : 0 < Real.log z := Real.log_pos (by linarith)
      calc 1 / (14 * L) ≤ 1 / (27 / 2 * Real.log z) := by
            apply one_div_le_one_div_of_le (by positivity); linarith
        _ = (z / (5 * Real.log z)) * (1 / ((27 / 10) * z)) := by
            field_simp; ring
        _ ≤ (((Ioc ⌊z⌋₊ ⌊(27 / 10 : ℝ) * z⌋₊).filter Nat.Prime).card : ℝ) *
              (1 / ((27 / 10) * z)) :=
            mul_le_mul_of_nonneg_right hcnt (by positivity)
        _ = ∑ p ∈ (Ioc ⌊z⌋₊ ⌊(27 / 10 : ℝ) * z⌋₊).filter Nat.Prime,
              (1 / ((27 / 10) * z) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ (Ioc ⌊z⌋₊ ⌊(27 / 10 : ℝ) * z⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
            apply Finset.sum_le_sum
            intro p hp
            have hp' := Finset.mem_filter.mp hp
            have hpI := Finset.mem_Ioc.mp hp'.1
            have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
            have hp_le : (p : ℝ) ≤ (27 / 10 : ℝ) * z :=
              le_trans (by exact_mod_cast hpI.2) (Nat.floor_le (by linarith))
            exact one_div_le_one_div_of_le hp_pos hp_le
    rw [Nat.cast_succ, add_div]
    exact add_le_add h1 hblock

/-! ## Products of primes from consecutive ranges -/

/-- `prodSet b k`: products `p₁ ⋯ p_k` with `pᵢ` prime in `(b (i-1), b i]`. -/
private def prodSet (b : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => {1}
  | k + 1 => (((Ioc (b k) (b (k + 1))).filter Nat.Prime) ×ˢ prodSet b k).image
      (fun x => x.1 * x.2)

private lemma mem_prodSet_succ {b : ℕ → ℕ} {k n : ℕ} : n ∈ prodSet b (k + 1) ↔
    ∃ p, (b k < p ∧ p ≤ b (k + 1)) ∧ p.Prime ∧ ∃ P ∈ prodSet b k, n = p * P := by
  simp only [prodSet, Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨p, P⟩, ⟨⟨hp1, hp2⟩, hP⟩, rfl⟩
    exact ⟨p, hp1, hp2, P, hP, rfl⟩
  · rintro ⟨p, hp1, hp2, P, hP, rfl⟩
    exact ⟨⟨p, P⟩, ⟨⟨hp1, hp2⟩, hP⟩, rfl⟩

private lemma prodSet_spec {b : ℕ → ℕ} (hb : Monotone b) (k : ℕ) : ∀ P ∈ prodSet b k,
    0 < P ∧ (∀ q, q.Prime → q ∣ P → b 0 < q ∧ q ≤ b k) ∧ (b 0 + 1) ^ k ≤ P ∧
      P ≤ b k ^ k ∧ PPSmooth (b k) P := by
  induction k with
  | zero =>
    intro P hP
    simp only [prodSet, Finset.mem_singleton] at hP
    subst hP
    refine ⟨one_pos, fun q hq hq1 => ?_, by simp, by simp, ppSmooth_one _⟩
    exact absurd (Nat.le_of_dvd one_pos hq1) (by have := hq.two_le; omega)
  | succ k ih =>
    intro n hn
    obtain ⟨p, ⟨hp1, hp2⟩, hp, P, hP, rfl⟩ := mem_prodSet_succ.mp hn
    obtain ⟨hP0, hPq, hPlo, hPhi, hPs⟩ := ih P hP
    have hbk : b k ≤ b (k + 1) := hb (Nat.le_succ k)
    have hb0 : b 0 ≤ b k := hb (Nat.zero_le k)
    have hpP : ¬ p ∣ P := fun h => by have := (hPq p hp h).2; omega
    refine ⟨Nat.mul_pos hp.pos hP0, ?_, ?_, ?_, ?_⟩
    · intro q hq hqd
      rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
        subst this; omega
      · have := hPq q hq h; omega
    · rw [pow_succ']
      exact Nat.mul_le_mul (by omega) hPlo
    · rw [pow_succ']
      exact Nat.mul_le_mul hp2 (le_trans hPhi (Nat.pow_le_pow_left hbk k))
    · exact PPSmooth.mul_coprime (ppSmooth_of_le hp.ne_zero hp2) (hPs.mono hbk) hp.ne_zero
        hP0.ne' ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpP)

private lemma prodSet_sum_ge {b : ℕ → ℕ} (hb : Monotone b) {σ : ℝ} (hσ : 0 ≤ σ) (k : ℕ)
    (hR : ∀ i < k, σ ≤ ∑ p ∈ Ioc (b i) (b (i + 1)), (if p.Prime then (1 : ℝ) / p else 0)) :
    σ ^ k ≤ ∑ P ∈ prodSet b k, (1 : ℝ) / P := by
  induction k with
  | zero => simp [prodSet]
  | succ k ih =>
    have ih' := ih (fun i hi => hR i (by omega))
    have hk := hR k (by omega)
    rw [← Finset.sum_filter] at hk
    have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2)
        ↑(((Ioc (b k) (b (k + 1))).filter Nat.Prime) ×ˢ prodSet b k) := by
      rintro ⟨p, P⟩ hx ⟨p', P'⟩ hx' heq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_Ioc] at hx hx'
      simp only at heq
      have hp := hx.1.2
      have hp' := hx'.1.2
      have hP'q := (prodSet_spec hb k P' hx'.2).2.1
      have hdvd : p ∣ p' * P' := heq ▸ dvd_mul_right p P
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · have hpp := (Nat.prime_dvd_prime_iff_eq hp hp').mp h
        subst hpp
        have := Nat.eq_of_mul_eq_mul_left hp.pos heq
        subst this; rfl
      · have := (hP'q p hp h).2; omega
    show σ ^ (k + 1) ≤ ∑ P ∈ (((Ioc (b k) (b (k + 1))).filter Nat.Prime) ×ˢ prodSet b k).image
      (fun x => x.1 * x.2), (1 : ℝ) / P
    rw [Finset.sum_image hinj, Finset.sum_product]
    have e : ∑ x ∈ (Ioc (b k) (b (k + 1))).filter Nat.Prime, ∑ y ∈ prodSet b k,
        (1 : ℝ) / ((x * y : ℕ) : ℝ) =
        (∑ x ∈ (Ioc (b k) (b (k + 1))).filter Nat.Prime, (1 : ℝ) / x) *
          ∑ y ∈ prodSet b k, (1 : ℝ) / y := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [Nat.cast_mul, one_div_mul_one_div]
    rw [e, pow_succ']
    exact mul_le_mul hk ih' (pow_nonneg hσ k) (le_trans hσ hk)

/-! ## Unique decomposition `n = P * t` -/

private lemma sigma_mul_injOn {T : Finset ℕ} {I : ℕ → Finset ℕ} (hT : ∀ P ∈ T, 0 < P)
    (hcop : ∀ P ∈ T, ∀ P' ∈ T, ∀ t ∈ I P', Nat.Coprime P t) :
    Set.InjOn (fun x : (_ : ℕ) × ℕ => x.1 * x.2) ↑(T.sigma I) := by
  rintro ⟨P, t⟩ hx ⟨P', t'⟩ hx' heq
  simp only [Finset.mem_coe, Finset.mem_sigma] at hx hx'
  simp only at heq
  have h1 : P ∣ P' := (hcop P hx.1 P' hx'.1 t' hx'.2).dvd_of_dvd_mul_right
    (heq ▸ dvd_mul_right P t)
  have h2 : P' ∣ P := (hcop P' hx'.1 P hx.1 t hx.2).dvd_of_dvd_mul_right
    (heq.symm ▸ dvd_mul_right P' t')
  have hPP := Nat.dvd_antisymm h1 h2
  subst hPP
  have := Nat.eq_of_mul_eq_mul_left (hT P hx.1) heq
  subst this; rfl

private lemma recipSum_cast (S : Finset ℕ) : ((recipSum S : ℚ) : ℝ) = ∑ n ∈ S, (1 : ℝ) / n := by
  simp [recipSum]

/-- Five consecutive ranges `(b i, b (i+1)]` above `x₀`, each of prime reciprocal sum
`≥ 1/5040`, ending below `x₀ u` (for `u` large and `u ≤ x₀`). -/
private lemma exists_ranges : ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ u : ℝ, U₀ ≤ u → ∀ x₀ : ℝ, u ≤ x₀ → x₀ ≤ u ^ 17 →
    ∃ b : ℕ → ℕ, Monotone b ∧ x₀ < (b 0 : ℝ) + 1 ∧ (b 5 : ℝ) ≤ x₀ * u ∧
      ∀ i < 5, (1 / 5040 : ℝ) ≤
        ∑ p ∈ Ioc (b i) (b (i + 1)), (if p.Prime then (1 : ℝ) / p else 0) := by
  obtain ⟨X₀, hX₀2, hX₀⟩ := exists_block_bound
  refine ⟨max X₀ (Real.exp 20), le_trans hX₀2 (le_max_left _ _), fun u hu x₀ hux hxu => ?_⟩
  have huX : X₀ ≤ u := le_trans (le_max_left _ _) hu
  have hue : Real.exp 20 ≤ u := le_trans (le_max_right _ _) hu
  have hu2 : 2 ≤ u := le_trans hX₀2 huX
  have hu0 : 0 < u := by linarith
  have hlogu : 20 ≤ Real.log u := by
    rw [← Real.log_exp 20]; exact Real.log_le_log (Real.exp_pos _) hue
  have hx0 : 0 < x₀ := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊Real.log u / 10⌋₊ := ⟨_, rfl⟩
  have hK2 : Real.log u / 20 ≤ (K : ℝ) := by
    have := Nat.sub_one_lt_floor (Real.log u / 10); rw [← hK] at this; linarith
  have hK1 : (K : ℝ) ≤ Real.log u / 10 := by rw [hK]; exact Nat.floor_le (by positivity)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (27 / 10 : ℝ) ^ K := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := hc ▸ one_le_pow₀ (by norm_num)
  have hc0 : 0 < c := by linarith
  have hc5 : c ^ 5 ≤ u := by
    rw [← Real.log_le_log_iff (pow_pos hc0 5) hu0, Real.log_pow, hc, Real.log_pow]
    have h1 : Real.log (27 / 10 : ℝ) ≤ 27 / 10 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    push_cast
    linarith
  refine ⟨fun i => ⌊c ^ i * x₀⌋₊, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 hij) hx0.le)
  · simp only [pow_zero, one_mul]
    exact Nat.lt_floor_add_one x₀
  · refine le_trans (Nat.floor_le (mul_nonneg (pow_pos hc0 5).le hx0.le)) ?_
    rw [mul_comm x₀ u]
    exact mul_le_mul_of_nonneg_right hc5 hx0.le
  · intro i hi
    have hci : c ^ (i + 1) * x₀ ≤ u * x₀ :=
      mul_le_mul_of_nonneg_right (le_trans (pow_le_pow_right₀ hc1 (by omega)) hc5) hx0.le
    have hxi : X₀ ≤ c ^ i * x₀ := by
      have h1 : 1 ≤ c ^ i := one_le_pow₀ hc1
      nlinarith
    have heq : c ^ (i + 1) * x₀ = (27 / 10 : ℝ) ^ K * (c ^ i * x₀) := by
      rw [pow_succ, hc]; ring
    have hlogL : Real.log ((27 / 10 : ℝ) ^ K * (c ^ i * x₀)) ≤ 18 * Real.log u := by
      rw [← heq]
      have h18 : c ^ (i + 1) * x₀ ≤ u ^ 18 := by
        have : u * x₀ ≤ u * u ^ 17 := mul_le_mul_of_nonneg_left hxu hu0.le
        calc c ^ (i + 1) * x₀ ≤ u * x₀ := hci
          _ ≤ u * u ^ 17 := this
          _ = u ^ 18 := by ring
      have := Real.log_le_log (mul_pos (pow_pos hc0 _) hx0) h18
      rw [Real.log_pow] at this
      push_cast at this
      exact this
    have hmain := hX₀ (c ^ i * x₀) hxi K (18 * Real.log u) (by positivity) hlogL
    show (1 / 5040 : ℝ) ≤ ∑ p ∈ Ioc ⌊c ^ i * x₀⌋₊ ⌊c ^ (i + 1) * x₀⌋₊,
      (if p.Prime then (1 : ℝ) / p else 0)
    rw [heq]
    refine le_trans ?_ hmain
    rw [le_div_iff₀ (by positivity)]
    linarith

/-- Core of `mass_smooth_ge`: the products `P * t`, `t ∈ (M/P, A/P]`, are distinct `y`-pp-smooth
elements of `(M, A]` and carry reciprocal mass `≥ (η/4) ∑_{P ∈ T} 1/P`. -/
private lemma mass_core {M A y b0 : ℕ} {η : ℝ} (T : Finset ℕ)
    (hT : ∀ P ∈ T, 0 < P ∧ (∀ q, q.Prime → q ∣ P → b0 < q) ∧ PPSmooth y P)
    (hb0y : b0 ≤ y) (hPbig : ∀ P ∈ T, A < P * (b0 + 1))
    (hPsmall : ∀ P ∈ T, 4 * (P : ℝ) ≤ η * M)
    (hA1 : (1 + η) * (M : ℝ) - 1 < A) (hA2 : A ≤ 2 * M) (hMpos : 0 < M) :
    (η / 4) * ∑ P ∈ T, (1 : ℝ) / P ≤ ∑ n ∈ (Ioc M A).filter (PPSmooth y), (1 : ℝ) / n := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have ht : ∀ P ∈ T, ∀ t ∈ Ioc (M / P) (A / P), 0 < t ∧ t ≤ b0 ∧ M < P * t ∧ P * t ≤ A := by
    intro P hP t htI
    have hP0 := (hT P hP).1
    rw [Finset.mem_Ioc] at htI
    have h1 : M < t * P := (Nat.div_lt_iff_lt_mul hP0).mp htI.1
    have h2 : t * P ≤ A := (Nat.le_div_iff_mul_le hP0).mp htI.2
    have h3 := hPbig P hP
    rw [mul_comm t P] at h1 h2
    refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h1), ?_, h1, h2⟩
    by_contra hcon
    push Not at hcon
    have : P * (b0 + 1) ≤ P * t := Nat.mul_le_mul_left P hcon
    omega
  have hcop : ∀ P ∈ T, ∀ P' ∈ T, ∀ t ∈ Ioc (M / P') (A / P'), Nat.Coprime P t := by
    intro P hP P' hP' t htI
    obtain ⟨ht0, htb, _, _⟩ := ht P' hP' t htI
    obtain ⟨_, hPq, _⟩ := hT P hP
    apply Nat.coprime_of_dvd
    intro k hk hkP hkt
    have := hPq k hk hkP
    have := Nat.le_of_dvd ht0 hkt
    omega
  have hinner : ∀ P ∈ T, (η / 4) * (1 / (P : ℝ)) ≤
      ∑ t ∈ Ioc (M / P) (A / P), (1 : ℝ) / ((P * t : ℕ) : ℝ) := by
    intro P hP
    have hP0 := (hT P hP).1
    have hPr : (0 : ℝ) < P := by exact_mod_cast hP0
    have hsmall := hPsmall P hP
    have hterm : ∀ t ∈ Ioc (M / P) (A / P),
        (1 : ℝ) / (2 * M) ≤ (1 : ℝ) / ((P * t : ℕ) : ℝ) := by
      intro t htI
      obtain ⟨ht0, _, _, hhi⟩ := ht P hP t htI
      apply one_div_le_one_div_of_le (by exact_mod_cast Nat.mul_pos hP0 ht0)
      have : P * t ≤ 2 * M := le_trans hhi hA2
      exact_mod_cast this
    have hcard : η * M / (2 * P) ≤ ((Ioc (M / P) (A / P)).card : ℝ) := by
      rw [Nat.card_Ioc]
      have e1 := natCast_sub_ge (A / P) (M / P)
      have e2 : (A : ℝ) / P - 1 < ((A / P : ℕ) : ℝ) := by
        rw [← Nat.floor_div_eq_div (K := ℝ)]; exact Nat.sub_one_lt_floor _
      have e3 : ((M / P : ℕ) : ℝ) ≤ (M : ℝ) / P := Nat.cast_div_le
      have e4 : ((1 + η) * M - 1) / P ≤ (A : ℝ) / P := div_le_div_of_nonneg_right hA1.le hPr.le
      have e5 : 1 / (P : ℝ) ≤ 1 := by
        rw [div_le_one hPr]; exact_mod_cast hP0
      have e6 : 4 ≤ η * M / P := by rw [le_div_iff₀ hPr]; linarith
      have e7 : ((1 + η) * M - 1) / P = M / P + η * M / P - 1 / P := by ring
      have e8 : η * M / (2 * P) = η * M / P / 2 := by ring
      linarith
    calc (η / 4) * (1 / (P : ℝ)) = (η * M / (2 * P)) * (1 / (2 * M)) := by
          field_simp; ring
      _ ≤ ((Ioc (M / P) (A / P)).card : ℝ) * (1 / (2 * M)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ∑ t ∈ Ioc (M / P) (A / P), (1 : ℝ) / (2 * M) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hterm
  have hinj := sigma_mul_injOn (T := T) (I := fun P => Ioc (M / P) (A / P))
    (fun P hP => (hT P hP).1) hcop
  have hsub : (T.sigma fun P => Ioc (M / P) (A / P)).image
      (fun x : (_ : ℕ) × ℕ => x.1 * x.2) ⊆ (Ioc M A).filter (PPSmooth y) := by
    intro n hn
    obtain ⟨⟨P, t⟩, hx, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_sigma] at hx
    obtain ⟨ht0, htb, hlo, hhi⟩ := ht P hx.1 t hx.2
    obtain ⟨hP0, _, hPs⟩ := hT P hx.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo, hhi⟩, ?_⟩
    exact PPSmooth.mul_coprime hPs (ppSmooth_of_le ht0.ne' (le_trans htb hb0y)) hP0.ne'
      ht0.ne' (hcop P hx.1 P hx.1 t hx.2)
  calc (η / 4) * ∑ P ∈ T, (1 : ℝ) / P = ∑ P ∈ T, (η / 4) * (1 / (P : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ P ∈ T, ∑ t ∈ Ioc (M / P) (A / P), (1 : ℝ) / ((P * t : ℕ) : ℝ) :=
        Finset.sum_le_sum hinner
    _ = ∑ x ∈ T.sigma (fun P => Ioc (M / P) (A / P)), (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ) :=
        (Finset.sum_sigma T (fun P => Ioc (M / P) (A / P))
          (fun x => (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ))).symm
    _ = ∑ n ∈ (T.sigma fun P => Ioc (M / P) (A / P)).image
          (fun x : (_ : ℕ) × ℕ => x.1 * x.2), (1 : ℝ) / n :=
        (Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / n) hinj).symm
    _ ≤ ∑ n ∈ (Ioc M A).filter (PPSmooth y), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-- Core of `card_smoothRough_ge`: the products `P * (Q k + 1)` are distinct `y`-pp-smooth,
`B`-rough elements of `(N₀, 2 N₀]`, at least `(N₀ / 2Q) ∑_{P ∈ T} 1/P` of them. -/
private lemma card_core {N0 B y b0 : ℕ} (T : Finset ℕ)
    (hT : ∀ P ∈ T, 0 < P ∧ (∀ q, q.Prime → q ∣ P → b0 < q) ∧ PPSmooth y P)
    (hb0y : b0 ≤ y) (hBb : B ≤ b0) (hPbig : ∀ P ∈ T, 2 * N0 < P * (b0 + 1))
    (hPsmall : ∀ P ∈ T, 4 * ((P : ℝ) * B.factorial) ≤ N0) :
    ((N0 : ℝ) / (2 * B.factorial)) * ∑ P ∈ T, (1 : ℝ) / P ≤
      (((Ioc N0 (2 * N0)).filter (fun n => PPSmooth y n ∧
          ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n)).card : ℝ) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = B.factorial := ⟨_, rfl⟩
  rw [← hQ] at hPsmall ⊢
  have hQ1 : 1 ≤ Q := hQ ▸ Nat.factorial_pos B
  obtain ⟨I, hI⟩ : ∃ I : ℕ → Finset ℕ, I = fun P =>
      (Ioo (N0 / (P * Q)) (2 * N0 / (P * Q))).image (fun k => Q * k + 1) := ⟨_, rfl⟩
  have ht : ∀ P ∈ T, ∀ t ∈ I P, 0 < t ∧ t ≤ b0 ∧ N0 < P * t ∧ P * t ≤ 2 * N0 ∧
      ∀ p, p.Prime → p ≤ B → ¬ p ∣ t := by
    intro P hP t htI
    rw [hI] at htI
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp htI
    rw [Finset.mem_Ioo] at hk
    have hP0 := (hT P hP).1
    have hPQ : 0 < P * Q := Nat.mul_pos hP0 hQ1
    have h1 : N0 < k * (P * Q) := (Nat.div_lt_iff_lt_mul hPQ).mp hk.1
    have h2 : (k + 1) * (P * Q) ≤ 2 * N0 := (Nat.le_div_iff_mul_le hPQ).mp hk.2
    have h3 : P * (Q * k + 1) = k * (P * Q) + P := by ring
    have h4 : P ≤ P * Q := Nat.le_mul_of_pos_right P hQ1
    have h5 : (k + 1) * (P * Q) = k * (P * Q) + P * Q := by ring
    have hlo : N0 < P * (Q * k + 1) := by omega
    have hhi : P * (Q * k + 1) ≤ 2 * N0 := by omega
    refine ⟨Nat.succ_pos _, ?_, hlo, hhi, ?_⟩
    · by_contra hcon
      push Not at hcon
      have : P * (b0 + 1) ≤ P * (Q * k + 1) := Nat.mul_le_mul_left P hcon
      have := hPbig P hP
      omega
    · intro p hp hpB hpt
      have hpQ : p ∣ Q := hQ ▸ Nat.dvd_factorial hp.pos hpB
      have : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_left hpQ k)).mp hpt
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hcop : ∀ P ∈ T, ∀ P' ∈ T, ∀ t ∈ I P', Nat.Coprime P t := by
    intro P hP P' hP' t htI
    obtain ⟨ht0, htb, _, _, _⟩ := ht P' hP' t htI
    obtain ⟨_, hPq, _⟩ := hT P hP
    apply Nat.coprime_of_dvd
    intro k hk hkP hkt
    have := hPq k hk hkP
    have := Nat.le_of_dvd ht0 hkt
    omega
  have hIcard : ∀ P ∈ T, (N0 : ℝ) / (2 * P * Q) ≤ ((I P).card : ℝ) := by
    intro P hP
    have hP0 := (hT P hP).1
    have hPQ : 0 < P * Q := Nat.mul_pos hP0 hQ1
    have hPQr : (0 : ℝ) < (P : ℝ) * Q := by exact_mod_cast hPQ
    have hinjk : Function.Injective (fun k : ℕ => Q * k + 1) := fun a b h =>
      Nat.eq_of_mul_eq_mul_left hQ1 (Nat.add_right_cancel h)
    rw [hI, Finset.card_image_of_injective _ hinjk, Nat.card_Ioo]
    have e1 := natCast_sub_ge (2 * N0 / (P * Q) - N0 / (P * Q)) 1
    have e2 := natCast_sub_ge (2 * N0 / (P * Q)) (N0 / (P * Q))
    have e3 : ((2 * N0 : ℕ) : ℝ) / ((P * Q : ℕ) : ℝ) - 1 < ((2 * N0 / (P * Q) : ℕ) : ℝ) := by
      rw [← Nat.floor_div_eq_div (K := ℝ)]; exact Nat.sub_one_lt_floor _
    have e4 : ((N0 / (P * Q) : ℕ) : ℝ) ≤ ((N0 : ℕ) : ℝ) / ((P * Q : ℕ) : ℝ) := Nat.cast_div_le
    push_cast at e1 e2 e3 e4 ⊢
    have e5 : 4 ≤ (N0 : ℝ) / (P * Q) := by rw [le_div_iff₀ hPQr]; linarith [hPsmall P hP]
    have e6 : (N0 : ℝ) / (2 * P * Q) = (N0 : ℝ) / (P * Q) / 2 := by ring
    have e7 : (2 * N0 : ℝ) / (P * Q) = 2 * ((N0 : ℝ) / (P * Q)) := by ring
    linarith
  have hinj := sigma_mul_injOn (T := T) (I := I) (fun P hP => (hT P hP).1) hcop
  have hsub : (T.sigma I).image (fun x : (_ : ℕ) × ℕ => x.1 * x.2) ⊆
      (Ioc N0 (2 * N0)).filter (fun n => PPSmooth y n ∧
          ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n) := by
    intro n hn
    obtain ⟨⟨P, t⟩, hx, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_sigma] at hx
    obtain ⟨ht0, htb, hlo, hhi, hrough⟩ := ht P hx.1 t hx.2
    obtain ⟨hP0, hPq, hPs⟩ := hT P hx.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo, hhi⟩, ?_, ?_⟩
    · exact PPSmooth.mul_coprime hPs (ppSmooth_of_le ht0.ne' (le_trans htb hb0y)) hP0.ne'
        ht0.ne' (hcop P hx.1 P hx.1 t hx.2)
    · intro p hpB hp hpd
      rw [Finset.mem_Iic] at hpB
      rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
      · have := hPq p hp h; omega
      · exact hrough p hp hpB h
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ1
  calc ((N0 : ℝ) / (2 * Q)) * ∑ P ∈ T, (1 : ℝ) / P = ∑ P ∈ T, (N0 : ℝ) / (2 * P * Q) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun P hP => ?_
        have : (P : ℝ) ≠ 0 := by exact_mod_cast (hT P hP).1.ne'
        field_simp
    _ ≤ ∑ P ∈ T, ((I P).card : ℝ) := Finset.sum_le_sum hIcard
    _ = (((T.sigma I).image (fun x : (_ : ℕ) × ℕ => x.1 * x.2)).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_sigma]
        push_cast
        rfl
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

/-- `y`-pp-smooth, `B`-rough integers in `(X, 2X]` with `X = M^{3/4} (log M)^4`. -/
theorem card_smoothRough_ge (B : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
    c * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4) ≤
      (((Ioc ⌊(M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4⌋₊
          ⌊2 * ((M : ℝ) ^ (3 / 4 : ℝ) * (Real.log M) ^ 4)⌋₊).filter
        (fun n => PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ n ∧
          ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n)).card : ℝ) := by
  obtain ⟨U₀, hU₀2, hU₀⟩ := exists_ranges
  have hQ1 : 1 ≤ B.factorial := Nat.factorial_pos B
  have hQr : (1 : ℝ) ≤ B.factorial := by exact_mod_cast hQ1
  refine ⟨(1 / 5040 : ℝ) ^ 4 / (4 * (B.factorial : ℝ)), by positivity, ?_⟩
  have hu : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hu.eventually_ge_atTop (max U₀ (max (B : ℝ) (4 * (B.factorial : ℝ) + 1))),
    hu.eventually (eventually_log_pow_le_mul_sqrt 4 (ε := 1 / 10 ^ 9) (by norm_num))]
    with M hM hlog4
  generalize hu_def : (M : ℝ) ^ (1 / 100 : ℝ) = u at hM hlog4
  have huU : U₀ ≤ u := le_trans (le_max_left _ _) hM
  have huB : (B : ℝ) ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have huQ : 4 * (B.factorial : ℝ) + 1 ≤ u :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have hu2 : 2 ≤ u := le_trans hU₀2 huU
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hu100 : u ^ 100 = (M : ℝ) := by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hy : (M : ℝ) ^ (1 / 5 : ℝ) = u ^ 20 := by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have h34 : (M : ℝ) ^ (3 / 4 : ℝ) = u ^ 75 := by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hlogM : Real.log M = 100 * Real.log u := by
    rw [← hu100, Real.log_pow]; push_cast; ring
  have hlogu : 1 / 2 ≤ Real.log u := by
    have h := Real.log_le_log (by norm_num) hu2
    linarith [Real.log_two_gt_d9]
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (M : ℝ) ^ (3 / 4 : ℝ) * Real.log M ^ 4 := ⟨_, rfl⟩
  rw [← hXdef]
  have hXu : X = u ^ 75 * (100 * Real.log u) ^ 4 := by rw [hXdef, h34, hlogM]
  have hX_lo : u ^ 75 ≤ X := by
    rw [hXu]
    have : 1 ≤ (100 * Real.log u) ^ 4 := one_le_pow₀ (by linarith)
    exact le_mul_of_one_le_right (pow_pos hu0 75).le this
  have hsq : √u ≤ u := by
    rw [Real.sqrt_le_left hu0.le]; nlinarith
  have hX_hi : 2 * X < u ^ 80 := by
    rw [hXu]
    have h1 : (100 * Real.log u) ^ 4 = 10 ^ 8 * Real.log u ^ 4 := by ring
    rw [h1]
    have h2 : 10 ^ 8 * Real.log u ^ 4 ≤ u / 10 := by
      calc 10 ^ 8 * Real.log u ^ 4 ≤ 10 ^ 8 * (1 / 10 ^ 9 * √u) := by gcongr
        _ = √u / 10 := by ring
        _ ≤ u / 10 := by linarith
    have h75 : 0 < u ^ 75 := pow_pos hu0 75
    have h4 := mul_le_mul_of_nonneg_left h2 h75.le
    have h3 : u ≤ u ^ 5 := le_self_pow₀ hu1 (by norm_num)
    have h5 := mul_lt_mul_of_pos_left (show u / 5 < u ^ 5 by linarith) h75
    calc 2 * (u ^ 75 * (10 ^ 8 * Real.log u ^ 4)) ≤ 2 * (u ^ 75 * (u / 10)) := by linarith
      _ = u ^ 75 * (u / 5) := by ring
      _ < u ^ 75 * u ^ 5 := h5
      _ = u ^ 80 := by ring
  have hux : u ≤ u ^ 16 := le_self_pow₀ hu1 (by norm_num)
  have hx17 : u ^ 16 ≤ u ^ 17 := pow_le_pow_right₀ hu1 (by norm_num)
  obtain ⟨b, hbmono, hb0, hb5, hR⟩ := hU₀ u huU (u ^ 16) hux hx17
  have hb4 : (b 4 : ℝ) ≤ u ^ 17 := by
    have h1 : (b 4 : ℝ) ≤ b 5 := by exact_mod_cast hbmono (by norm_num : 4 ≤ 5)
    have h2 : u ^ 16 * u = u ^ 17 := by ring
    linarith
  have hb4y : b 4 ≤ ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ := by
    rw [hy]; apply Nat.le_floor
    exact le_trans hb4 (pow_le_pow_right₀ hu1 (by norm_num))
  have hb04 : b 0 ≤ b 4 := hbmono (by norm_num)
  have hBb : B ≤ b 0 := by
    have h1 : (B : ℝ) < b 0 + 1 := by linarith
    have h2 : B < b 0 + 1 := by exact_mod_cast h1
    omega
  have hTsum := prodSet_sum_ge hbmono (by norm_num : (0 : ℝ) ≤ 1 / 5040) 4
    (fun i hi => hR i (by omega))
  have hTspec := prodSet_spec hbmono 4
  have hX0 : 0 ≤ X := le_trans (pow_pos hu0 75).le hX_lo
  have hN0le : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0
  have hN0gt : X - 1 < ⌊X⌋₊ := Nat.sub_one_lt_floor X
  have hN1 : (1 : ℝ) ≤ ⌊X⌋₊ := by
    have : u ≤ u ^ 75 := le_self_pow₀ hu1 (by norm_num)
    linarith
  have hPbig : ∀ P ∈ prodSet b 4, 2 * ⌊X⌋₊ < P * (b 0 + 1) := by
    intro P hP
    obtain ⟨_, _, hlo, _, _⟩ := hTspec P hP
    have hlo' : ((b 0 : ℝ) + 1) ^ 4 ≤ P := by exact_mod_cast hlo
    have h5 : (u ^ 16) ^ 5 < ((b 0 : ℝ) + 1) ^ 5 :=
      pow_lt_pow_left₀ hb0 (by positivity) (by norm_num)
    have : (2 * ⌊X⌋₊ : ℝ) < P * ((b 0 : ℝ) + 1) := by
      calc (2 * ⌊X⌋₊ : ℝ) ≤ 2 * X := by linarith
        _ < u ^ 80 := hX_hi
        _ = (u ^ 16) ^ 5 := by ring
        _ < ((b 0 : ℝ) + 1) ^ 5 := h5
        _ = ((b 0 : ℝ) + 1) ^ 4 * ((b 0 : ℝ) + 1) := by ring
        _ ≤ P * ((b 0 : ℝ) + 1) := mul_le_mul_of_nonneg_right hlo' (by positivity)
    exact_mod_cast this
  have hPsmall : ∀ P ∈ prodSet b 4, 4 * ((P : ℝ) * B.factorial) ≤ ⌊X⌋₊ := by
    intro P hP
    obtain ⟨_, _, _, hhi, _⟩ := hTspec P hP
    have hhi' : (P : ℝ) ≤ (b 4 : ℝ) ^ 4 := by exact_mod_cast hhi
    have h68 : (P : ℝ) ≤ u ^ 68 := by
      calc (P : ℝ) ≤ (b 4 : ℝ) ^ 4 := hhi'
        _ ≤ (u ^ 17) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hb4 4
        _ = u ^ 68 := by ring
    have hQ0 : (0 : ℝ) ≤ B.factorial := by positivity
    have h7 : u ≤ u ^ 7 := le_self_pow₀ hu1 (by norm_num)
    have h68' : 1 ≤ u ^ 68 := one_le_pow₀ hu1
    have k1 : (4 * (B.factorial : ℝ) + 1) * u ^ 68 ≤ u ^ 75 := by
      calc (4 * (B.factorial : ℝ) + 1) * u ^ 68 ≤ u * u ^ 68 :=
            mul_le_mul_of_nonneg_right huQ (by positivity)
        _ ≤ u ^ 7 * u ^ 68 := mul_le_mul_of_nonneg_right h7 (by positivity)
        _ = u ^ 75 := by ring
    have k2 : (P : ℝ) * B.factorial ≤ u ^ 68 * B.factorial :=
      mul_le_mul_of_nonneg_right h68 hQ0
    linarith
  have hcore := card_core (N0 := ⌊X⌋₊) (B := B) (y := ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊) (b0 := b 0)
    (prodSet b 4)
    (fun P hP => ⟨(hTspec P hP).1, fun q hq hqP => ((hTspec P hP).2.1 q hq hqP).1,
      ((hTspec P hP).2.2.2.2).mono hb4y⟩)
    (le_trans hb04 hb4y) hBb hPbig hPsmall
  have h2N : 2 * ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := by
    apply Nat.le_floor; push_cast; linarith
  have hsub : (Ioc ⌊X⌋₊ (2 * ⌊X⌋₊)).filter (fun n => PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ n ∧
        ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n) ⊆
      (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ n ∧
        ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n) :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right h2N)
  calc (1 / 5040 : ℝ) ^ 4 / (4 * (B.factorial : ℝ)) * X
      ≤ (1 / 5040 : ℝ) ^ 4 / (4 * (B.factorial : ℝ)) * (2 * ⌊X⌋₊) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ = ((⌊X⌋₊ : ℝ) / (2 * B.factorial)) * (1 / 5040) ^ 4 := by ring
    _ ≤ ((⌊X⌋₊ : ℝ) / (2 * B.factorial)) * ∑ P ∈ prodSet b 4, (1 : ℝ) / P :=
        mul_le_mul_of_nonneg_left hTsum (by positivity)
    _ ≤ _ := hcore
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

/-- `y`-pp-smooth integers in `(M, (1+η) M]` have reciprocal mass `≥ κ η`. -/
theorem mass_smooth_ge : ∃ κ : ℝ, 0 < κ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ᶠ M : ℕ in atTop,
    κ * η ≤ ((recipSum ((Ioc M ⌊(1 + η) * M⌋₊).filter
      (PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊)) : ℚ) : ℝ) := by
  obtain ⟨U₀, hU₀2, hU₀⟩ := exists_ranges
  refine ⟨(1 / 5040 : ℝ) ^ 5 / 4, by positivity, fun η hη hη1 => ?_⟩
  have hu : Tendsto (fun M : ℕ => (M : ℝ) ^ (1 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hu.eventually_ge_atTop (max U₀ (4 / η))] with M hM
  generalize hu_def : (M : ℝ) ^ (1 / 100 : ℝ) = u at hM
  have huU : U₀ ≤ u := le_trans (le_max_left _ _) hM
  have hu4 : 4 / η ≤ u := le_trans (le_max_right _ _) hM
  have hu2 : 2 ≤ u := le_trans hU₀2 huU
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hu100 : u ^ 100 = (M : ℝ) := by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hy : (M : ℝ) ^ (1 / 5 : ℝ) = u ^ 20 := by
    rw [← hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
  have hMpos : (0 : ℝ) < M := by rw [← hu100]; positivity
  have hux : u ≤ u ^ 17 := le_self_pow₀ hu1 (by norm_num)
  obtain ⟨b, hbmono, hb0, hb5, hR⟩ := hU₀ u huU (u ^ 17) hux le_rfl
  have hb5' : (b 5 : ℝ) ≤ u ^ 18 := by
    have h2 : u ^ 17 * u = u ^ 18 := by ring
    linarith
  have hb5y : b 5 ≤ ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ := by
    rw [hy]
    apply Nat.le_floor
    exact le_trans hb5' (pow_le_pow_right₀ hu1 (by norm_num))
  have hb05 : b 0 ≤ b 5 := hbmono (by norm_num)
  have hTsum := prodSet_sum_ge hbmono (by norm_num : (0 : ℝ) ≤ 1 / 5040) 5 hR
  have hTspec := prodSet_spec hbmono 5
  have hA1 : (1 + η) * (M : ℝ) - 1 < (⌊(1 + η) * (M : ℝ)⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have hA2 : ⌊(1 + η) * (M : ℝ)⌋₊ ≤ 2 * M := by
    have h1 : (⌊(1 + η) * (M : ℝ)⌋₊ : ℝ) ≤ (1 + η) * M :=
      Nat.floor_le (mul_nonneg (by linarith) hM0)
    have h2 : (1 + η) * (M : ℝ) ≤ 2 * M := by nlinarith
    have : (⌊(1 + η) * (M : ℝ)⌋₊ : ℝ) ≤ 2 * M := le_trans h1 h2
    exact_mod_cast this
  have hPbig : ∀ P ∈ prodSet b 5, ⌊(1 + η) * (M : ℝ)⌋₊ < P * (b 0 + 1) := by
    intro P hP
    obtain ⟨_, _, hlo, _, _⟩ := hTspec P hP
    have hlo' : ((b 0 : ℝ) + 1) ^ 5 ≤ P := by exact_mod_cast hlo
    have h6 : (u ^ 17) ^ 6 < ((b 0 : ℝ) + 1) ^ 6 :=
      pow_lt_pow_left₀ hb0 (by positivity) (by norm_num)
    have hu2' : 4 ≤ u ^ 2 := by nlinarith
    have h4M : 4 * (M : ℝ) ≤ u ^ 2 * u ^ 100 := by
      rw [hu100]; exact mul_le_mul_of_nonneg_right hu2' hM0
    have : (2 * M : ℝ) < P * ((b 0 : ℝ) + 1) := by
      calc (2 * M : ℝ) < u ^ 2 * u ^ 100 := by linarith
        _ = (u ^ 17) ^ 6 := by ring
        _ < ((b 0 : ℝ) + 1) ^ 6 := h6
        _ = ((b 0 : ℝ) + 1) ^ 5 * ((b 0 : ℝ) + 1) := by ring
        _ ≤ P * ((b 0 : ℝ) + 1) := mul_le_mul_of_nonneg_right hlo' (by positivity)
    have h2M : 2 * M < P * (b 0 + 1) := by exact_mod_cast this
    omega
  have hPsmall : ∀ P ∈ prodSet b 5, 4 * (P : ℝ) ≤ η * M := by
    intro P hP
    obtain ⟨_, _, _, hhi, _⟩ := hTspec P hP
    have hhi' : (P : ℝ) ≤ (b 5 : ℝ) ^ 5 := by exact_mod_cast hhi
    have h90 : (P : ℝ) ≤ u ^ 90 := by
      calc (P : ℝ) ≤ (b 5 : ℝ) ^ 5 := hhi'
        _ ≤ (u ^ 18) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hb5' 5
        _ = u ^ 90 := by ring
    have h1 : 4 ≤ u * η := (div_le_iff₀ hη).mp hu4
    have h2 : u ≤ u ^ 10 := le_self_pow₀ hu1 (by norm_num)
    have hηu : 4 ≤ η * u ^ 10 := by
      have := mul_le_mul_of_nonneg_left h2 hη.le
      linarith
    have h3 : 4 * u ^ 90 ≤ η * u ^ 10 * u ^ 90 :=
      mul_le_mul_of_nonneg_right hηu (pow_pos hu0 90).le
    calc 4 * (P : ℝ) ≤ 4 * u ^ 90 := by linarith
      _ ≤ η * u ^ 10 * u ^ 90 := h3
      _ = η * M := by rw [← hu100]; ring
  have hcore := mass_core (M := M) (A := ⌊(1 + η) * (M : ℝ)⌋₊)
    (y := ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊) (b0 := b 0) (η := η) (prodSet b 5)
    (fun P hP => ⟨(hTspec P hP).1, fun q hq hqP => ((hTspec P hP).2.1 q hq hqP).1,
      ((hTspec P hP).2.2.2.2).mono hb5y⟩)
    (le_trans hb05 hb5y) hPbig hPsmall hA1 hA2 (by exact_mod_cast hMpos)
  rw [recipSum_cast]
  calc (1 / 5040 : ℝ) ^ 5 / 4 * η = (η / 4) * (1 / 5040) ^ 5 := by ring
    _ ≤ (η / 4) * ∑ P ∈ prodSet b 5, (1 : ℝ) / P :=
        mul_le_mul_of_nonneg_left hTsum (by positivity)
    _ ≤ _ := hcore

end Croot
