import Croot.Basic
import Croot.Primes

/-!
# Existence of pp-smooth numbers in dyadic-type ranges, avoiding a prime

For large `y`, every real `Z` with `1/4 ≤ Z ≤ y ^ 12` and every prime `p`, there is a
`y`-pp-smooth `s` with `Z ≤ s ≤ 4 Z` and `p ∤ s`.

(Without an upper bound on `Z` the statement would be false: every `y`-pp-smooth number divides
`lcm(1, …, y)`.)

Construction: if `Z ≤ y/3` use a power of `2` (or of `3` when `p = 2`), or `1` if `Z < 1`;
otherwise multiply by a prime `P ∈ (y/3, y]` with `P ≠ p` taken from a fixed finite set `T`
of such primes (each used at most once) and recurse on `Z / P`.  Since `Z ≤ y ^ k ≤ (y/3) ^ (2k)`
for `y ≥ 9`, a set `T` of `2k` primes suffices, and for large `y` there are that many primes in
`(y/3, y]` by `Croot.eventually_card_primes_Ioc_ge`.

Main results:
* `Croot.exists_ppSmooth_coprime_pow`: the statement for `Z ≤ y ^ k`, any fixed `k`;
* `Croot.exists_ppSmooth_coprime`: the case `k = 12`.
-/

namespace Croot

open Real Finset Filter

/-- A positive integer `n ≤ y` is `y`-pp-smooth. -/
lemma ppSmooth_of_le {y n : ℕ} (hn : n ≠ 0) (h : n ≤ y) : PPSmooth y n := fun p _ =>
  (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.ordProj_dvd n p)).trans h

/-- Multiplying a `y`-pp-smooth number by a new prime `P ≤ y` keeps it `y`-pp-smooth. -/
lemma PPSmooth.prime_mul {y s P : ℕ} (h : PPSmooth y s) (hs : s ≠ 0) (hP : P.Prime)
    (hPy : P ≤ y) (hPs : ¬ P ∣ s) : PPSmooth y (P * s) := by
  intro r hr
  rw [Nat.primeFactors_mul hP.ne_zero hs, Finset.mem_union, hP.primeFactors,
    Finset.mem_singleton] at hr
  rw [Nat.factorization_mul hP.ne_zero hs, Finsupp.add_apply]
  rcases hr with hrP | hr
  · subst hrP
    rw [hP.factorization_self, Nat.factorization_eq_zero_of_not_dvd hPs, add_zero, pow_one]
    exact hPy
  · have hrP : r ≠ P := fun hrP => hPs (by rw [← hrP]; exact Nat.dvd_of_mem_primeFactors hr)
    rw [hP.factorization, Finsupp.single_apply, if_neg (Ne.symm hrP), zero_add]
    exact h r hr

/-- Base case of the construction: for `1/4 ≤ Z ≤ y/3` take `1` or a power of `2` or `3`. -/
lemma exists_ppSmooth_base {y p : ℕ} (hp : p.Prime) {Z : ℝ} (hZ1 : 1 / 4 ≤ Z)
    (hZ2 : Z ≤ (y : ℝ) / 3) :
    ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y s ∧ ¬ p ∣ s ∧
      ∀ r : ℕ, r.Prime → r ∣ s → r ≤ 3 := by
  rcases lt_or_ge Z 1 with hZ | hZ
  · refine ⟨1, by rw [Nat.cast_one]; exact hZ.le, by rw [Nat.cast_one]; linarith,
      ppSmooth_one y, hp.not_dvd_one, ?_⟩
    intro r hr hr1
    exact absurd hr1 hr.not_dvd_one
  · obtain ⟨q, hq, hq3, hqp⟩ : ∃ q : ℕ, q.Prime ∧ q ≤ 3 ∧ q ≠ p := by
      by_cases h : p = 2
      · exact ⟨3, Nat.prime_three, le_rfl, by omega⟩
      · exact ⟨2, Nat.prime_two, by norm_num, fun h' => h h'.symm⟩
    have hZ0 : (0 : ℝ) ≤ Z := by linarith
    have hn0 : ⌊Z⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊Z⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hZ)
      omega
    set a := Nat.log q ⌊Z⌋₊ with ha
    have h1 : ⌊Z⌋₊ < q ^ (a + 1) := Nat.lt_pow_succ_log_self hq.one_lt _
    have h2 : q ^ a ≤ ⌊Z⌋₊ := Nat.pow_log_le_self q hn0
    have hlo : Z ≤ ((q ^ (a + 1) : ℕ) : ℝ) := by
      have h1' : ⌊Z⌋₊ + 1 ≤ q ^ (a + 1) := h1
      have : ((⌊Z⌋₊ + 1 : ℕ) : ℝ) ≤ ((q ^ (a + 1) : ℕ) : ℝ) := by exact_mod_cast h1'
      have h3 := Nat.lt_floor_add_one Z
      push_cast at this ⊢
      linarith
    have hhi : ((q ^ (a + 1) : ℕ) : ℝ) ≤ 3 * Z := by
      have h4 : q ^ (a + 1) ≤ 3 * ⌊Z⌋₊ := by
        rw [pow_succ]
        calc q ^ a * q ≤ ⌊Z⌋₊ * 3 := Nat.mul_le_mul h2 hq3
          _ = 3 * ⌊Z⌋₊ := Nat.mul_comm _ _
      have h5 : (⌊Z⌋₊ : ℝ) ≤ Z := Nat.floor_le hZ0
      have : ((q ^ (a + 1) : ℕ) : ℝ) ≤ ((3 * ⌊Z⌋₊ : ℕ) : ℝ) := by exact_mod_cast h4
      push_cast at this ⊢
      linarith
    refine ⟨q ^ (a + 1), hlo, by linarith, ?_, ?_, ?_⟩
    · apply ppSmooth_of_le (pow_ne_zero _ hq.ne_zero)
      have : ((q ^ (a + 1) : ℕ) : ℝ) ≤ (y : ℝ) := by linarith
      exact_mod_cast this
    · intro hdvd
      exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)).symm
    · intro r hr hdvd
      rw [(Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow hdvd)]
      exact hq3

/-- The recursive construction, by induction on the finite set `T` of available primes in
`(y/3, y]`: each prime of `T` is used at most once, which keeps the exact prime powers `≤ y`. -/
lemma exists_ppSmooth_aux {y p : ℕ} (hp : p.Prime) (hy : 9 ≤ y) :
    ∀ T : Finset ℕ, (∀ P ∈ T, P.Prime ∧ (y : ℝ) / 3 < P ∧ P ≤ y ∧ P ≠ p) →
    ∀ Z : ℝ, 1 / 4 ≤ Z → Z ≤ ((y : ℝ) / 3) ^ (T.card + 1) →
      ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y s ∧ ¬ p ∣ s ∧
        ∀ r : ℕ, r.Prime → r ∣ s → r ∈ T ∨ r ≤ 3 := by
  have hy9 : (9 : ℝ) ≤ y := by exact_mod_cast hy
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ Z hZ1 hZ2
    rw [Finset.card_empty, zero_add, pow_one] at hZ2
    obtain ⟨s, h1, h2, h3, h4, h5⟩ := exists_ppSmooth_base hp hZ1 hZ2
    exact ⟨s, h1, h2, h3, h4, fun r hr hrs => Or.inr (h5 r hr hrs)⟩
  | insert P T hPT ih =>
    intro hT Z hZ1 hZ2
    by_cases hZ : Z ≤ (y : ℝ) / 3
    · obtain ⟨s, h1, h2, h3, h4, h5⟩ := exists_ppSmooth_base hp hZ1 hZ
      exact ⟨s, h1, h2, h3, h4, fun r hr hrs => Or.inr (h5 r hr hrs)⟩
    rw [not_le] at hZ
    obtain ⟨hPp, hPlo, hPhi, hPne⟩ := hT P (Finset.mem_insert_self P T)
    have hT' : ∀ P' ∈ T, P'.Prime ∧ (y : ℝ) / 3 < P' ∧ P' ≤ y ∧ P' ≠ p :=
      fun P' h => hT P' (Finset.mem_insert_of_mem h)
    have hPy : (P : ℝ) ≤ y := by exact_mod_cast hPhi
    have hP0 : (0 : ℝ) < P := by linarith
    have hP3 : 3 < P := by
      have : (3 : ℝ) < P := by linarith
      exact_mod_cast this
    rw [Finset.card_insert_of_notMem hPT] at hZ2
    have hZ'1 : 1 / 4 ≤ Z / P := by
      rw [le_div_iff₀ hP0]; linarith
    have hZ'2 : Z / P ≤ ((y : ℝ) / 3) ^ (T.card + 1) := by
      rw [div_le_iff₀ hP0]
      have hpow0 : (0 : ℝ) ≤ ((y : ℝ) / 3) ^ (T.card + 1) := by positivity
      calc Z ≤ ((y : ℝ) / 3) ^ (T.card + 1 + 1) := hZ2
        _ = ((y : ℝ) / 3) ^ (T.card + 1) * ((y : ℝ) / 3) := pow_succ _ _
        _ ≤ ((y : ℝ) / 3) ^ (T.card + 1) * P := mul_le_mul_of_nonneg_left hPlo.le hpow0
    obtain ⟨s, h1, h2, h3, h4, h5⟩ := ih hT' (Z / P) hZ'1 hZ'2
    have hs0 : s ≠ 0 := by
      have : (0 : ℝ) < s := by linarith
      exact_mod_cast this.ne'
    have hPs : ¬ P ∣ s := by
      intro hdvd
      rcases h5 P hPp hdvd with h | h
      · exact hPT h
      · omega
    refine ⟨P * s, ?_, ?_, h3.prime_mul hs0 hPp hPhi hPs, ?_, ?_⟩
    · rw [div_le_iff₀ hP0] at h1
      push_cast
      linarith
    · push_cast
      calc (P : ℝ) * s ≤ P * (4 * (Z / P)) := mul_le_mul_of_nonneg_left h2 hP0.le
        _ = 4 * Z := by field_simp
    · intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact hPne ((Nat.prime_dvd_prime_iff_eq hp hPp).mp h).symm
      · exact h4 h
    · intro r hr hdvd
      rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
      · left
        rw [(Nat.prime_dvd_prime_iff_eq hr hPp).mp h]
        exact Finset.mem_insert_self P T
      · rcases h5 r hr h with h' | h'
        · exact Or.inl (Finset.mem_insert_of_mem h')
        · exact Or.inr h'

/-- For every `m`, eventually `m ≤ x / (5 log x)`. -/
lemma eventually_natCast_le_div_log (m : ℕ) :
    ∀ᶠ x : ℝ in atTop, (m : ℝ) ≤ x / (5 * Real.log x) := by
  have hc : (0 : ℝ) < 1 / (5 * ((m : ℝ) + 1)) := by positivity
  filter_upwards [Real.isLittleO_log_id_atTop.bound hc, eventually_ge_atTop (3 : ℝ)]
    with x hx hx3
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : Real.log x ≤ 1 / (5 * ((m : ℝ) + 1)) * x := by
    have h := hx
    simp only [id, Real.norm_eq_abs] at h
    rwa [abs_of_pos hlog, abs_of_pos hx0] at h
  have h2 : 5 * ((m : ℝ) + 1) * Real.log x ≤ x := by
    calc 5 * ((m : ℝ) + 1) * Real.log x
        ≤ 5 * ((m : ℝ) + 1) * (1 / (5 * ((m : ℝ) + 1)) * x) := by gcongr
      _ = x := by field_simp
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- For every `m`, eventually there are at least `m` primes in `(⌊10 y / 27⌋, y] ⊆ (y/3, y]`. -/
lemma eventually_card_primes_third_ge (m : ℕ) : ∀ᶠ y : ℕ in atTop,
    m ≤ ((Ioc ⌊(10 / 27 : ℝ) * y⌋₊ y).filter Nat.Prime).card := by
  have ht : Tendsto (fun y : ℕ => (10 / 27 : ℝ) * y) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  filter_upwards [ht.eventually (eventually_card_primes_Ioc_ge.and
    (eventually_natCast_le_div_log m))] with y hy
  obtain ⟨h1, h2⟩ := hy
  have e : (27 / 10 : ℝ) * ((10 / 27 : ℝ) * y) = y := by ring
  rw [e, Nat.floor_natCast] at h1
  have : (m : ℝ) ≤ (((Ioc ⌊(10 / 27 : ℝ) * y⌋₊ y).filter Nat.Prime).card : ℝ) := h2.trans h1
  exact_mod_cast this

/-- Existence of `y`-pp-smooth numbers in `[Z, 4 Z]` coprime to a given prime, for
`1/4 ≤ Z ≤ y ^ k` (any fixed exponent `k`) and all large `y`. -/
theorem exists_ppSmooth_coprime_pow (k : ℕ) : ∀ᶠ y : ℕ in atTop, ∀ p : ℕ, p.Prime →
    ∀ Z : ℝ, 1 / 4 ≤ Z → Z ≤ (y : ℝ) ^ k →
      ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y s ∧ ¬ p ∣ s := by
  filter_upwards [eventually_card_primes_third_ge (2 * k + 1), eventually_ge_atTop 9]
    with y hcard hy9 p hp Z hZ1 hZ2
  have hy9' : (9 : ℝ) ≤ y := by exact_mod_cast hy9
  set S := (Ioc ⌊(10 / 27 : ℝ) * y⌋₊ y).filter Nat.Prime with hS
  set T := S.erase p with hT
  have hTcard : 2 * k ≤ T.card := by
    have h : S.card - 1 ≤ T.card := Finset.pred_card_le_card_erase
    omega
  have hTprop : ∀ P ∈ T, P.Prime ∧ (y : ℝ) / 3 < P ∧ P ≤ y ∧ P ≠ p := by
    intro P hP
    rw [hT, Finset.mem_erase, hS, Finset.mem_filter, Finset.mem_Ioc] at hP
    obtain ⟨hPp, ⟨hlo, hhi⟩, hprime⟩ := hP
    refine ⟨hprime, ?_, hhi, hPp⟩
    have h := (Nat.floor_lt (by positivity)).mp hlo
    linarith
  have hZ' : Z ≤ ((y : ℝ) / 3) ^ (T.card + 1) := by
    have h3 : (1 : ℝ) ≤ (y : ℝ) / 3 := by linarith
    have hy0 : (0 : ℝ) ≤ y := by linarith
    calc Z ≤ (y : ℝ) ^ k := hZ2
      _ ≤ (((y : ℝ) / 3) ^ 2) ^ k := by
          apply pow_le_pow_left₀ hy0
          nlinarith
      _ = ((y : ℝ) / 3) ^ (2 * k) := by rw [← pow_mul]
      _ ≤ ((y : ℝ) / 3) ^ (T.card + 1) := pow_le_pow_right₀ h3 (by omega)
  obtain ⟨s, h1, h2, h3, h4, -⟩ := exists_ppSmooth_aux hp hy9 T hTprop Z hZ1 hZ'
  exact ⟨s, h1, h2, h3, h4⟩

/-- For large `y`, every prime `p` and every real `Z` with `1/4 ≤ Z ≤ y ^ 12`, there is a
`y`-pp-smooth `s` with `Z ≤ s ≤ 4 Z` and `p ∤ s`. -/
theorem exists_ppSmooth_coprime : ∀ᶠ y : ℕ in atTop, ∀ p : ℕ, p.Prime → ∀ Z : ℝ, 1 / 4 ≤ Z →
    Z ≤ (y : ℝ) ^ 12 → ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y s ∧ ¬ p ∣ s :=
  exists_ppSmooth_coprime_pow 12

end Croot
