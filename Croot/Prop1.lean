import Croot.Basic
import Croot.Primes
import Croot.Lemma1
import Croot.SmoothExist
import Croot.ElimAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Croot's Proposition 1: clearing large prime powers from the denominator

From the harmonic block `(N, M]` (with `e N ≤ M ≤ e N + 3`) we remove a set `D` of small
reciprocal mass so that the reduced denominator of `∑_{n ∈ (N,M] \ D} 1/n` is
`⌊N^{1/12}⌋`-pp-smooth.  We also keep `D` large enough (it contains all primes in `(N, M]`)
so that the residual `1 - ∑` is not too small.

## Proof outline

Write `H(S) = ∑_{n ∈ S} 1/n`, `I = (N, M]`, `Q = ⌊N / (log N)^4⌋`, `y₁ = ⌊N^{1/12}⌋`.

* `D₀ = bigPP N M Q` is the set of `n ∈ I` that are not `Q`-pp-smooth.  It contains every prime
  of `(N, 2.7 N]`, so `H(D₀) ≥ 1/(15 log N)` (`recipSum_bigPP_ge`), and every element of it is
  divisible by a prime power in `(Q, 3N]`, so `H(D₀) → 0` (`recipSum_bigPP_le`).
* Downward induction on the threshold `t` from `Q` to `y₁` (`clear_all`) maintaining
  `ClearInv`: if the denominator of `H(I \ D)` is `t`-pp-smooth but not `(t-1)`-pp-smooth, then
  `t = p^a` exactly divides it; we choose a `y₁`-pp-smooth `s ≈ N / (t (log t)^4)` coprime to
  `p` and a set `R` of `≥ (log t)^{3.9}` primes `r ∈ (N/(ts), 2.7 N/(ts)]` (`exists_s_R`), and
  Lemma 1 gives `T ⊆ R` such that removing `{t s r : r ∈ T}` kills the factor `p^a`
  (`den_sub_sum_dvd`), at a cost of at most `3 (log N)^4 / N` in mass (`step_main`).
* The total extra mass is `≤ #{prime powers ≤ Q} · 3 (log N)^4 / N → 0`.
-/

namespace Croot

open Real Finset Filter

namespace P1

/-! ## Arithmetic facts about pp-smoothness -/

lemma ppSmooth_prime {y r : ℕ} (hr : r.Prime) (hry : r ≤ y) : PPSmooth y r := by
  intro q hq
  rw [hr.primeFactors, Finset.mem_singleton] at hq
  subst hq
  rw [hr.factorization_self, pow_one]
  exact hry

lemma ppSmooth_primePow {y p a : ℕ} (hp : p.Prime) (h : p ^ a ≤ y) : PPSmooth y (p ^ a) := by
  intro q hq
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hq' : q = p :=
    (Nat.prime_dvd_prime_iff_eq hqprime hp).1
      (hqprime.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq))
  subst hq'
  rw [hqprime.factorization_pow, Finsupp.single_eq_same]
  exact h

lemma ppSmooth_mul_of_coprime {y a b : ℕ} (ha : PPSmooth y a) (hb : PPSmooth y b) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hab : Nat.Coprime a b) : PPSmooth y (a * b) := by
  rw [← hab.lcm_eq_mul]
  exact ppSmooth_of_dvd_lcmUpto (Nat.lcm_dvd (ha.dvd_lcmUpto ha0) (hb.dvd_lcmUpto hb0))

lemma not_ppSmooth_primePow_mul {p a c : ℕ} (hp : p.Prime) (ha : 0 < a) (hc : c ≠ 0)
    (hpc : ¬ p ∣ c) : ¬ PPSmooth (p ^ a - 1) (p ^ a * c) := by
  intro h
  have hmem : p ∈ (p ^ a * c).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hp, dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _,
      mul_ne_zero (pow_ne_zero _ hp.ne_zero) hc⟩
  have h1 := h p hmem
  have hfac : (p ^ a * c).factorization p = a := by
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hc, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpc,
      add_zero]
  rw [hfac] at h1
  have : 1 ≤ p ^ a := Nat.one_le_pow _ _ hp.pos
  omega

lemma ppSmooth_sub_one_of_not_dvd {p a v : ℕ} (hp : p.Prime) (h : PPSmooth (p ^ a) v)
    (hv : ¬ p ∣ v) : PPSmooth (p ^ a - 1) v := by
  intro q hq
  have h1 := h q hq
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hqv := Nat.dvd_of_mem_primeFactors hq
  have hv0 : v ≠ 0 := (Nat.mem_primeFactors.1 hq).2.2
  have hqp : q ≠ p := fun e => hv (e ▸ hqv)
  have hne : q ^ v.factorization q ≠ p ^ a := by
    intro e
    have hk : v.factorization q ≠ 0 := (hqprime.factorization_pos_of_dvd hv0 hqv).ne'
    have : q ∣ p ^ a := e ▸ dvd_pow_self q hk
    exact hqp ((Nat.prime_dvd_prime_iff_eq hqprime hp).1 (hqprime.dvd_of_dvd_pow this))
  omega

lemma exists_primePow_eq_of_not_ppSmooth {t n : ℕ} (h : PPSmooth t n)
    (h' : ¬ PPSmooth (t - 1) n) : ∃ p ∈ n.primeFactors, p ^ n.factorization p = t := by
  simp only [PPSmooth, not_forall, not_le, exists_prop] at h'
  obtain ⟨p, hp, hlt⟩ := h'
  exact ⟨p, hp, le_antisymm (h p hp) (by omega)⟩

lemma card_primeFactors_le_log {s : ℕ} (hs : 0 < s) :
    (s.primeFactors.card : ℝ) ≤ Real.log s / Real.log 2 := by
  have h1 : 2 ^ s.primeFactors.card ≤ ∏ p ∈ s.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ s.primeFactors, p ≤ s := Nat.le_of_dvd hs (Nat.prod_primeFactors_dvd s)
  have h3 : ((2 : ℝ) ^ s.primeFactors.card) ≤ s := by exact_mod_cast h1.trans h2
  rw [le_div_iff₀ (Real.log_pos one_lt_two)]
  have := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at this

/-! ## Reciprocal sums -/

lemma recipSum_cast (S : Finset ℕ) : (recipSum S : ℝ) = ∑ n ∈ S, (1 : ℝ) / n := by
  simp [recipSum]

lemma recipSum_le_card_div {S : Finset ℕ} {N : ℕ} (hN : 0 < N) (h : ∀ n ∈ S, N < n) :
    (recipSum S : ℝ) ≤ S.card / N := by
  rw [recipSum_cast]
  calc ∑ n ∈ S, (1 : ℝ) / n ≤ ∑ n ∈ S, (1 : ℝ) / N := by
        apply Finset.sum_le_sum
        intro n hn
        apply one_div_le_one_div_of_le (by exact_mod_cast hN)
        exact_mod_cast (h n hn).le
    _ = S.card / N := by rw [Finset.sum_const, nsmul_eq_mul]; ring

lemma card_multiples_Ioc_le {N M q : ℕ} (hq : 0 < q) :
    ((Ioc N M).filter (fun n => q ∣ n)).card ≤ M / q - N / q := by
  calc ((Ioc N M).filter (fun n => q ∣ n)).card
      ≤ ((Ioc (N / q) (M / q)).image (fun k => q * k)).card := by
        apply Finset.card_le_card
        intro n hn
        rw [Finset.mem_filter, Finset.mem_Ioc] at hn
        obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
        rw [Finset.mem_image]
        refine ⟨k, Finset.mem_Ioc.2 ⟨?_, ?_⟩, rfl⟩
        · exact (Nat.div_lt_iff_lt_mul hq).2 (by rw [mul_comm]; exact h1)
        · exact (Nat.le_div_iff_mul_le hq).2 (by rw [mul_comm]; exact h2)
    _ ≤ (Ioc (N / q) (M / q)).card := Finset.card_image_le
    _ = M / q - N / q := Nat.card_Ioc _ _

lemma card_multiples_Ioc_le_real {N M q : ℕ} (hq : 0 < q) (hNM : N ≤ M) :
    (((Ioc N M).filter (fun n => q ∣ n)).card : ℝ) ≤ ((M : ℝ) - N) / q + 1 := by
  have h1 := card_multiples_Ioc_le (N := N) (M := M) hq
  have h2 : N / q ≤ M / q := Nat.div_le_div_right hNM
  have h3 : (((Ioc N M).filter (fun n => q ∣ n)).card : ℝ) ≤
      ((M / q : ℕ) : ℝ) - ((N / q : ℕ) : ℝ) := by
    rw [← Nat.cast_sub h2]; exact_mod_cast h1
  have h4 : ((M / q : ℕ) : ℝ) ≤ (M : ℝ) / q := Nat.cast_div_le
  have h5 : (N : ℝ) / q - 1 < ((N / q : ℕ) : ℝ) := by
    have := Nat.sub_one_lt_floor ((N : ℝ) / q)
    rwa [Nat.floor_div_eq_div] at this
  have : ((M : ℝ) - N) / q = (M : ℝ) / q - (N : ℝ) / q := sub_div _ _ _
  linarith

/-! ## The set of non-`Q`-pp-smooth elements of `(N, M]` -/

open Classical in
/-- The elements of `(N, M]` that are not `Q`-pp-smooth. -/
noncomputable def bigPP (N M Q : ℕ) : Finset ℕ := (Ioc N M).filter (fun n => ¬ PPSmooth Q n)

lemma mem_bigPP {N M Q n : ℕ} : n ∈ bigPP N M Q ↔ n ∈ Ioc N M ∧ ¬ PPSmooth Q n := by
  rw [bigPP, Finset.mem_filter]

lemma recipSum_bigPP_le {N M Q : ℕ} (hN : 0 < N) (hNM : N ≤ M) (hM : M ≤ 3 * N) :
    (recipSum (bigPP N M Q) : ℝ) ≤
      2 * ∑ q ∈ (Ioc Q (3 * N)).filter IsPrimePow, (1 : ℝ) / q +
        (((Ioc Q (3 * N)).filter IsPrimePow).card : ℝ) / N := by
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, P = (Ioc Q (3 * N)).filter IsPrimePow := ⟨_, rfl⟩
  rw [← hP]
  -- each element of `bigPP` has an exact prime-power divisor in `P`
  have hex : ∀ n ∈ bigPP N M Q, ∃ q ∈ P, q ∣ n := by
    intro n hn
    rw [mem_bigPP, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn1, hn2⟩, hns⟩ := hn
    simp only [PPSmooth, not_forall, not_le, exists_prop] at hns
    obtain ⟨p, hp, hlt⟩ := hns
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hn0 : n ≠ 0 := by omega
    refine ⟨p ^ n.factorization p, ?_, Nat.ordProj_dvd n p⟩
    rw [hP, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨hlt, ?_⟩, ?_⟩
    · exact (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)).trans (hn2.trans hM)
    · exact (isPrimePow_nat_iff _).2
        ⟨p, _, hpp, hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp), rfl⟩
  have hfirst : (recipSum (bigPP N M Q) : ℝ) ≤
      ∑ q ∈ P, (recipSum ((Ioc N M).filter (fun n => q ∣ n)) : ℝ) := by
    rw [recipSum_cast]
    calc ∑ n ∈ bigPP N M Q, (1 : ℝ) / n
        ≤ ∑ n ∈ bigPP N M Q, ∑ q ∈ P, (if q ∣ n then (1 : ℝ) / n else 0) := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨q, hq, hqn⟩ := hex n hn
          calc (1 : ℝ) / n = (if q ∣ n then (1 : ℝ) / n else 0) := by rw [if_pos hqn]
            _ ≤ ∑ q ∈ P, (if q ∣ n then (1 : ℝ) / n else 0) :=
              Finset.single_le_sum (f := fun q => if q ∣ n then (1 : ℝ) / n else 0)
                (fun q _ => by split_ifs <;> positivity) hq
      _ = ∑ q ∈ P, ∑ n ∈ bigPP N M Q, (if q ∣ n then (1 : ℝ) / n else 0) := Finset.sum_comm
      _ = ∑ q ∈ P, ∑ n ∈ (bigPP N M Q).filter (fun n => q ∣ n), (1 : ℝ) / n := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_filter]
      _ ≤ ∑ q ∈ P, ∑ n ∈ (Ioc N M).filter (fun n => q ∣ n), (1 : ℝ) / n := by
          apply Finset.sum_le_sum
          intro q _
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset_filter _ (fun n hn => (mem_bigPP.1 hn).1)
          · intro _ _ _; positivity
      _ = ∑ q ∈ P, (recipSum ((Ioc N M).filter (fun n => q ∣ n)) : ℝ) := by
          simp only [recipSum_cast]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsecond : ∀ q ∈ P,
      (recipSum ((Ioc N M).filter (fun n => q ∣ n)) : ℝ) ≤ 2 / q + 1 / N := by
    intro q hq
    have hq0 : 0 < q := by
      rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hq; omega
    have h1 := recipSum_le_card_div hN (S := (Ioc N M).filter (fun n => q ∣ n))
      (fun n hn => (Finset.mem_Ioc.1 (Finset.mem_filter.1 hn).1).1)
    have h2 := card_multiples_Ioc_le_real (N := N) (M := M) hq0 hNM
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
    have hM' : (M : ℝ) ≤ 3 * N := by exact_mod_cast hM
    calc (recipSum ((Ioc N M).filter (fun n => q ∣ n)) : ℝ)
        ≤ (((Ioc N M).filter (fun n => q ∣ n)).card : ℝ) / N := h1
      _ ≤ (((M : ℝ) - N) / q + 1) / N := by gcongr
      _ ≤ ((2 * N) / q + 1) / N := by gcongr; linarith
      _ = 2 / q + 1 / N := by field_simp
  calc (recipSum (bigPP N M Q) : ℝ)
      ≤ ∑ q ∈ P, (recipSum ((Ioc N M).filter (fun n => q ∣ n)) : ℝ) := hfirst
    _ ≤ ∑ q ∈ P, (2 / (q : ℝ) + 1 / N) := Finset.sum_le_sum hsecond
    _ = 2 * ∑ q ∈ P, (1 : ℝ) / q + (P.card : ℝ) / N := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      congr 1
      · exact Finset.sum_congr rfl fun q _ => by ring
      · ring

lemma recipSum_bigPP_ge {N M Q : ℕ} (hN : 0 < N) (hlogN : 0 < Real.log N) (hQN : Q ≤ N)
    (hM27 : (27 / 10 : ℝ) * N ≤ M) (hM3 : (M : ℝ) ≤ 3 * N)
    (hprime : (N : ℝ) / (5 * Real.log N) ≤
      (((Ioc ⌊(N : ℝ)⌋₊ ⌊(27 / 10 : ℝ) * N⌋₊).filter Nat.Prime).card : ℝ)) :
    1 / (15 * Real.log N) ≤ (recipSum (bigPP N M Q) : ℝ) := by
  rw [Nat.floor_natCast] at hprime
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, P = (Ioc N ⌊(27 / 10 : ℝ) * N⌋₊).filter Nat.Prime :=
    ⟨_, rfl⟩
  rw [← hP] at hprime
  have hfl : ⌊(27 / 10 : ℝ) * N⌋₊ ≤ M := Nat.floor_le_of_le hM27
  have hPsub : P ⊆ bigPP N M Q := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hp1, hp2⟩, hpp⟩ := hp
    rw [mem_bigPP, Finset.mem_Ioc]
    refine ⟨⟨hp1, hp2.trans hfl⟩, fun hsm => ?_⟩
    have := hsm p (by rw [hpp.primeFactors]; exact Finset.mem_singleton_self p)
    rw [hpp.factorization_self, pow_one] at this
    omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : ∀ p ∈ P, (1 : ℝ) / (3 * N) ≤ 1 / (p : ℝ) := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp0 : (0 : ℝ) < p := by
      have : 0 < p := by omega
      exact_mod_cast this
    apply one_div_le_one_div_of_le hp0
    have : (p : ℝ) ≤ M := by exact_mod_cast hp.1.2.trans hfl
    linarith
  have hl0 : Real.log N ≠ 0 := hlogN.ne'
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  calc 1 / (15 * Real.log N) = (N / (5 * Real.log N)) * (1 / (3 * N)) := by
        field_simp
        ring
    _ ≤ (P.card : ℝ) * (1 / (3 * N)) := by gcongr
    _ = ∑ p ∈ P, (1 : ℝ) / (3 * N) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ P, (1 : ℝ) / p := Finset.sum_le_sum hle
    _ = (recipSum P : ℝ) := (recipSum_cast P).symm
    _ ≤ (recipSum (bigPP N M Q) : ℝ) := by exact_mod_cast recipSum_mono hPsub

/-! ## The invariant of the elimination procedure -/

/-- The invariant at threshold `t`: `D₀ ⊆ D ⊆ (N, M]`, no element of `D` is `t`-pp-smooth,
the denominator of `H((N, M] \ D)` is `t`-pp-smooth, and the mass of `D` is controlled. -/
def ClearInv (N M Q : ℕ) (D₀ : Finset ℕ) (B : ℝ) (t : ℕ) (D : Finset ℕ) : Prop :=
  D₀ ⊆ D ∧ D ⊆ Ioc N M ∧ (∀ n ∈ D, ¬ PPSmooth t n) ∧
    PPSmooth t (recipSum (Ioc N M \ D)).den ∧
    (recipSum D : ℝ) ≤ (recipSum D₀ : ℝ) + (((Ioc t Q).filter IsPrimePow).card : ℝ) * B

lemma clearInv_base {N M Q : ℕ} {B : ℝ} : ClearInv N M Q (bigPP N M Q) B Q (bigPP N M Q) := by
  refine ⟨subset_rfl, fun n hn => (mem_bigPP.1 hn).1, fun n hn => (mem_bigPP.1 hn).2, ?_, ?_⟩
  · apply ppSmooth_den_recipSum
    · intro n hn
      rw [Finset.mem_sdiff] at hn
      by_contra h
      exact hn.2 (mem_bigPP.2 ⟨hn.1, h⟩)
    · intro h0
      rw [Finset.mem_sdiff, Finset.mem_Ioc] at h0
      omega
  · simp

lemma clearInv_sub_one {N M Q t : ℕ} {D₀ D : Finset ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hInv : ClearInv N M Q D₀ B t D) (hsm : PPSmooth (t - 1) (recipSum (Ioc N M \ D)).den) :
    ClearInv N M Q D₀ B (t - 1) D := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hInv
  refine ⟨h1, h2, fun n hn hn' => h3 n hn (hn'.mono (Nat.sub_le _ _)), hsm, h5.trans ?_⟩
  have hc : ((Ioc t Q).filter IsPrimePow).card ≤ ((Ioc (t - 1) Q).filter IsPrimePow).card :=
    Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.sub_le _ _)))
  have hc' : (((Ioc t Q).filter IsPrimePow).card : ℝ) ≤
      ((Ioc (t - 1) Q).filter IsPrimePow).card := by exact_mod_cast hc
  linarith [mul_le_mul_of_nonneg_right hc' hB]

lemma clear_all {N M Q y₁ : ℕ} {D₀ : Finset ℕ} {B : ℝ}
    (hstep : ∀ t D, y₁ < t → t ≤ Q → ClearInv N M Q D₀ B t D →
      ∃ D', ClearInv N M Q D₀ B (t - 1) D')
    (hbase : ClearInv N M Q D₀ B Q D₀) :
    ∃ D, ClearInv N M Q D₀ B (Q - (Q - y₁)) D := by
  have key : ∀ j, j ≤ Q - y₁ → ∃ D, ClearInv N M Q D₀ B (Q - j) D := by
    intro j
    induction j with
    | zero => intro _; exact ⟨D₀, by rw [Nat.sub_zero]; exact hbase⟩
    | succ j ih =>
      intro hj
      obtain ⟨D, hD⟩ := ih (by omega)
      obtain ⟨D', hD'⟩ := hstep (Q - j) D (by omega) (by omega) hD
      exact ⟨D', by rwa [show Q - (j + 1) = Q - j - 1 by omega]⟩
  exact key _ le_rfl

/-! ## The analytic input of one elimination step -/

lemma exists_s_R {N M t y₁ p : ℕ} {x₀ : ℝ}
    (hprimes : ∀ x : ℝ, x₀ ≤ x → x / (5 * Real.log x) ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ))
    (hSE : ∀ p : ℕ, p.Prime → ∀ Z : ℝ, 1 / 4 ≤ Z → Z ≤ (y₁ : ℝ) ^ 12 →
      ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y₁ s ∧ ¬ p ∣ s)
    (hy10 : (10 : ℝ) ≤ y₁) (hyt : (y₁ : ℝ) + 1 ≤ t) (hNy : (N : ℝ) < ((y₁ : ℝ) + 1) ^ 12)
    (hp : p.Prime) (hN0 : 0 < N)
    (hM : (27 / 10 : ℝ) * N ≤ M)
    (htN : (t : ℝ) ≤ N / Real.log N ^ 4)
    (hNt : Real.log N ≤ 12 * Real.log t)
    (hN1 : 1 < Real.log N)
    (ht4 : 4 ≤ t) (h3 : 3 * Real.log t ^ 4 < t) (hL1 : 1 ≤ Real.log t)
    (hLx : x₀ ≤ Real.log t ^ 4 / 4) (hL2 : 2 ≤ Real.log t ^ 4 / 4)
    (hcount : Real.log t ^ (39 / 10 : ℝ) ≤
      Real.log t ^ 4 / (80 * Real.log (Real.log t)) - 18 * Real.log t - 1) :
    ∃ s : ℕ, ∃ R : Finset ℕ, 0 < s ∧ ¬ p ∣ s ∧ PPSmooth y₁ s ∧
      (∀ r ∈ R, r.Prime ∧ ¬ r ∣ s ∧ r ≠ p ∧ N < t * s * r ∧ t * s * r ≤ M ∧ r < t ∧
        Real.log t ^ 4 / 4 ≤ r ∧ (r : ℝ) ≤ 3 * Real.log t ^ 4) ∧
      Real.log t ^ (39 / 10 : ℝ) ≤ R.card ∧ (R.card : ℝ) ≤ 3 * Real.log N ^ 4 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have ht4r : (4 : ℝ) ≤ t := by exact_mod_cast ht4
  have hlogN4 : 1 ≤ Real.log N ^ 4 := one_le_pow₀ hN1.le
  have htN' : (t : ℝ) ≤ N := htN.trans (div_le_self hNr.le hlogN4)
  have hLN' : Real.log t ≤ Real.log N := Real.log_le_log ht0 htN'
  obtain ⟨L, hLdef⟩ : ∃ L, Real.log t = L := ⟨_, rfl⟩
  rw [hLdef] at h3 hL1 hLx hL2 hcount hNt hLN' ⊢
  have hL0 : 0 < L := by linarith
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hL4N : L ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ hL0.le hLN' 4
  -- the parameter `Z`
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = N / (t * L ^ 4) := ⟨_, rfl⟩
  have htL : 0 < (t : ℝ) * L ^ 4 := by positivity
  have hZpos : 0 < Z := by rw [hZ]; exact div_pos hNr htL
  have htZ : (t : ℝ) * L ^ 4 * Z = N := by rw [hZ]; field_simp
  have hZ1 : 1 ≤ Z := by
    rw [hZ, le_div_iff₀ htL, one_mul]
    calc (t : ℝ) * L ^ 4 ≤ N / Real.log N ^ 4 * Real.log N ^ 4 :=
          mul_le_mul htN hL4N (by positivity) (by positivity)
      _ = N := by field_simp
  -- `Z ≤ y₁ ^ 12`, as required by the existence of smooth numbers
  have hZy : Z ≤ (y₁ : ℝ) ^ 12 := by
    have hy0 : (0 : ℝ) < (y₁ : ℝ) + 1 := by linarith
    have h1 : Z * ((y₁ : ℝ) + 1) ≤ N := by
      have htt : (y₁ : ℝ) + 1 ≤ t * L ^ 4 := hyt.trans (le_mul_of_one_le_right ht0.le hL4)
      calc Z * ((y₁ : ℝ) + 1) ≤ Z * (t * L ^ 4) := mul_le_mul_of_nonneg_left htt hZpos.le
        _ = N := by rw [← htZ]; ring
    have h2 : Z < ((y₁ : ℝ) + 1) ^ 11 := by
      have : Z * ((y₁ : ℝ) + 1) < ((y₁ : ℝ) + 1) ^ 11 * ((y₁ : ℝ) + 1) := by
        calc Z * ((y₁ : ℝ) + 1) ≤ N := h1
          _ < ((y₁ : ℝ) + 1) ^ 12 := hNy
          _ = ((y₁ : ℝ) + 1) ^ 11 * ((y₁ : ℝ) + 1) := by ring
      exact lt_of_mul_lt_mul_right this hy0.le
    have h8 : 0 ≤ (y₁ : ℝ) ^ 11 := by positivity
    have h3 : ((y₁ : ℝ) + 1) ^ 11 ≤ (y₁ : ℝ) ^ 12 := by
      calc ((y₁ : ℝ) + 1) ^ 11 ≤ (11 / 10 * (y₁ : ℝ)) ^ 11 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 11
        _ = (11 / 10) ^ 11 * (y₁ : ℝ) ^ 11 := mul_pow _ _ _
        _ ≤ 3 * (y₁ : ℝ) ^ 11 := mul_le_mul_of_nonneg_right (by norm_num) h8
        _ ≤ (y₁ : ℝ) * (y₁ : ℝ) ^ 11 := mul_le_mul_of_nonneg_right (by linarith) h8
        _ = (y₁ : ℝ) ^ 12 := by ring
    linarith
  obtain ⟨s, hZs, hs4Z, hsy, hps⟩ := hSE p hp Z (by linarith) hZy
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hZpos hZs
  have hs0' : 0 < s := by exact_mod_cast hs0
  -- the parameter `X = N / (t s)`
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = N / (t * s) := ⟨_, rfl⟩
  have hts : 0 < (t : ℝ) * s := by positivity
  have hXts : X * (t * s) = N := by rw [hX]; field_simp
  have hXle : X ≤ L ^ 4 := by
    rw [hX, div_le_iff₀ hts]
    calc (N : ℝ) = t * L ^ 4 * Z := htZ.symm
      _ ≤ t * L ^ 4 * s := by gcongr
      _ = L ^ 4 * (t * s) := by ring
  have hXge : L ^ 4 / 4 ≤ X := by
    rw [hX, le_div_iff₀ hts]
    calc L ^ 4 / 4 * (t * s) ≤ L ^ 4 / 4 * (t * (4 * Z)) := by gcongr
      _ = t * L ^ 4 * Z := by ring
      _ = N := htZ
  have hX2 : 2 ≤ X := hL2.trans hXge
  have hX0 : 0 < X := by linarith
  -- the primes in `(X, 2.7 X]`
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, P = (Ioc ⌊X⌋₊ ⌊(27 / 10 : ℝ) * X⌋₊).filter Nat.Prime :=
    ⟨_, rfl⟩
  have hPcard : X / (5 * Real.log X) ≤ P.card := by
    rw [hP]; exact hprimes X (hLx.trans hXge)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogX' : Real.log X ≤ 4 * Real.log L := by
    simpa [Real.log_pow] using Real.log_le_log hX0 hXle
  have hPcard' : L ^ 4 / (80 * Real.log L) ≤ P.card := by
    calc L ^ 4 / (80 * Real.log L) = (L ^ 4 / 4) / (5 * (4 * Real.log L)) := by ring
      _ ≤ X / (5 * Real.log X) := div_le_div₀ hX0.le hXge (by linarith) (by linarith)
      _ ≤ P.card := hPcard
  -- remove the primes dividing `s`, and `p`
  obtain ⟨R, hR⟩ : ∃ R : Finset ℕ, R = P.filter (fun r => ¬ r ∣ s ∧ r ≠ p) := ⟨_, rfl⟩
  have hPsub : P ⊆ R ∪ (s.primeFactors ∪ {p}) := by
    intro r hr
    by_cases h1 : r ∣ s
    · have hrp : r.Prime := by rw [hP, Finset.mem_filter] at hr; exact hr.2
      exact Finset.mem_union_right _
        (Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hrp, h1, hs0'.ne'⟩))
    · by_cases h2 : r = p
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton.2 h2))
      · exact Finset.mem_union_left _ (by rw [hR]; exact Finset.mem_filter.2 ⟨hr, h1, h2⟩)
  have hcardP : (P.card : ℝ) ≤ R.card + s.primeFactors.card + 1 := by
    have h1 : P.card ≤ R.card + (s.primeFactors.card + 1) :=
      (Finset.card_le_card hPsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
          (by rw [Finset.card_singleton])) _))
    have h2 : (P.card : ℝ) ≤ R.card + (s.primeFactors.card + 1) := by exact_mod_cast h1
    linarith
  have hsN : (s : ℝ) ≤ N := by
    have htL4 : 4 ≤ (t : ℝ) * L ^ 4 := ht4r.trans (le_mul_of_one_le_right ht0.le hL4)
    have h4Z : 4 * Z ≤ N := by
      rw [hZ, mul_div_assoc', div_le_iff₀ htL]
      calc 4 * (N : ℝ) = N * 4 := by ring
        _ ≤ N * (t * L ^ 4) := mul_le_mul_of_nonneg_left htL4 hNr.le
    linarith
  have homega : (s.primeFactors.card : ℝ) ≤ 18 * L := by
    have h1 := card_primeFactors_le_log hs0'
    have hlog2 : (2 : ℝ) / 3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hlogs : Real.log s ≤ 12 * L := (Real.log_le_log hs0 hsN).trans hNt
    calc (s.primeFactors.card : ℝ) ≤ Real.log s / Real.log 2 := h1
      _ ≤ 12 * L / (2 / 3) := div_le_div₀ (by linarith) hlogs (by norm_num) hlog2.le
      _ = 18 * L := by ring
  refine ⟨s, R, hs0', hps, hsy, ?_, ?_, ?_⟩
  · intro r hr
    rw [hR, Finset.mem_filter, hP, Finset.mem_filter, Finset.mem_Ioc] at hr
    obtain ⟨⟨⟨hr1, hr2⟩, hrp⟩, hrs, hrne⟩ := hr
    have hXr : X < r := (Nat.floor_lt hX0.le).1 hr1
    have hrX : (r : ℝ) ≤ 27 / 10 * X :=
      (Nat.cast_le.2 hr2).trans (Nat.floor_le (by positivity))
    refine ⟨hrp, hrs, hrne, ?_, ?_, ?_, ?_, ?_⟩
    · have : (N : ℝ) < t * s * r := by
        rw [← hXts]
        calc X * (t * s) < r * (t * s) := mul_lt_mul_of_pos_right hXr hts
          _ = t * s * r := by ring
      exact_mod_cast this
    · have : (t : ℝ) * s * r ≤ M := by
        calc (t : ℝ) * s * r ≤ t * s * (27 / 10 * X) := by gcongr
          _ = 27 / 10 * N := by rw [← hXts]; ring
          _ ≤ M := hM
      exact_mod_cast this
    · have : (r : ℝ) < t := by linarith
      exact_mod_cast this
    · linarith
    · linarith
  · linarith
  · have h1 : R.card ≤ (Ioc ⌊X⌋₊ ⌊(27 / 10 : ℝ) * X⌋₊).card := by
      rw [hR, hP]
      exact (Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)
    rw [Nat.card_Ioc] at h1
    have h2 : ⌊X⌋₊ ≤ ⌊(27 / 10 : ℝ) * X⌋₊ := Nat.floor_le_floor (by linarith)
    have h3' : (R.card : ℝ) ≤ (⌊(27 / 10 : ℝ) * X⌋₊ : ℝ) - ⌊X⌋₊ := by
      rw [← Nat.cast_sub h2]; exact_mod_cast h1
    have h4 : (⌊(27 / 10 : ℝ) * X⌋₊ : ℝ) ≤ 27 / 10 * X := Nat.floor_le (by positivity)
    have h5 : X - 1 < (⌊X⌋₊ : ℝ) := Nat.sub_one_lt_floor X
    linarith

/-! ## One elimination step -/

lemma step_main {N M Q y₁ t : ℕ} {D₀ D : Finset ℕ} {x₀ B : ℝ}
    (hprimes : ∀ x : ℝ, x₀ ≤ x → x / (5 * Real.log x) ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ))
    (hSE : ∀ p : ℕ, p.Prime → ∀ Z : ℝ, 1 / 4 ≤ Z → Z ≤ (y₁ : ℝ) ^ 12 →
      ∃ s : ℕ, Z ≤ s ∧ (s : ℝ) ≤ 4 * Z ∧ PPSmooth y₁ s ∧ ¬ p ∣ s)
    (hy10 : (10 : ℝ) ≤ y₁) (hNy : (N : ℝ) < ((y₁ : ℝ) + 1) ^ 12)
    (hL1 : ∀ R : Finset ℕ, (∀ r ∈ R, r.Prime ∧ ¬ r ∣ t ∧ (Real.log t) ^ 4 / 4 ≤ r ∧
      (r : ℝ) ≤ 3 * (Real.log t) ^ 4) → (Real.log t) ^ (39 / 10 : ℝ) ≤ R.card →
      ∀ c : ZMod t, ∃ T ⊆ R, ∑ r ∈ T, ((r : ZMod t))⁻¹ = c)
    (hB : B = 3 * Real.log N ^ 4 / N)
    (hN0 : 0 < N)
    (hM : (27 / 10 : ℝ) * N ≤ M)
    (htN : (t : ℝ) ≤ N / Real.log N ^ 4)
    (hNt : Real.log N ≤ 12 * Real.log t)
    (hN1 : 1 < Real.log N)
    (hyt : y₁ < t) (htQ : t ≤ Q)
    (hconds : 4 ≤ t ∧ 3 * Real.log t ^ 4 < t ∧ 1 ≤ Real.log t ∧ x₀ ≤ Real.log t ^ 4 / 4 ∧
      2 ≤ Real.log t ^ 4 / 4 ∧
      Real.log t ^ (39 / 10 : ℝ) ≤
        Real.log t ^ 4 / (80 * Real.log (Real.log t)) - 18 * Real.log t - 1)
    (hInv : ClearInv N M Q D₀ B t D)
    (hns : ¬ PPSmooth (t - 1) (recipSum (Ioc N M \ D)).den) :
    ∃ D', ClearInv N M Q D₀ B (t - 1) D' := by
  obtain ⟨ht4, h3, hL1', hLx, hL2, hcount⟩ := hconds
  obtain ⟨hD0, hDI, hDns, hsm, hmass⟩ := hInv
  obtain ⟨p, hpmem, hpt⟩ := exists_primePow_eq_of_not_ppSmooth hsm hns
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  -- the step data `s`, `R`
  have hyt' : (y₁ : ℝ) + 1 ≤ t := by exact_mod_cast hyt
  obtain ⟨s, R, hs0, hps, hsy, hR, hRcard, hRcard'⟩ :=
    exists_s_R hprimes hSE hy10 hyt' hNy hp hN0 hM htN hNt hN1 ht4 h3 hL1' hLx hL2 hcount
  obtain ⟨x, hx⟩ : ∃ x : ℚ, recipSum (Ioc N M \ D) = x := ⟨_, rfl⟩
  rw [hx] at hsm hns hpmem hpt
  have hden0 : x.den ≠ 0 := x.den_nz
  obtain ⟨a, ha_def⟩ : ∃ a, x.den.factorization p = a := ⟨_, rfl⟩
  have ha : 0 < a := by
    rw [← ha_def]; exact hp.factorization_pos_of_dvd hden0 (Nat.dvd_of_mem_primeFactors hpmem)
  rw [ha_def] at hpt
  obtain ⟨v', hv'_def⟩ : ∃ v', x.den / p ^ a = v' := ⟨_, rfl⟩
  have hden : x.den = p ^ a * v' := by
    rw [← hv'_def, ← ha_def]; exact (Nat.ordProj_mul_ordCompl_eq_self x.den p).symm
  have hv' : ¬ p ∣ v' := by
    rw [← hv'_def, ← ha_def]; exact Nat.not_dvd_ordCompl hp hden0
  subst hpt
  -- apply Lemma 1 modulo `p ^ a`
  have hRt : ∀ r ∈ R, r.Prime ∧ ¬ r ∣ p ^ a ∧ (Real.log ((p ^ a : ℕ) : ℝ)) ^ 4 / 4 ≤ r ∧
      (r : ℝ) ≤ 3 * (Real.log ((p ^ a : ℕ) : ℝ)) ^ 4 := by
    intro r hr
    obtain ⟨hrp, -, hrne, -, -, -, hr1, hr2⟩ := hR r hr
    refine ⟨hrp, fun hdvd => hrne ?_, hr1, hr2⟩
    exact (Nat.prime_dvd_prime_iff_eq hrp hp).1 (hrp.dvd_of_dvd_pow hdvd)
  obtain ⟨TR, hTR, hTsum⟩ := hL1 R hRt hRcard
    ((x.num : ZMod (p ^ a)) * ((v' : ZMod (p ^ a)))⁻¹ * (s : ZMod (p ^ a)))
  have hTR' : ∀ r ∈ TR, r.Prime ∧ ¬ r ∣ s ∧ r ≠ p ∧ N < p ^ a * s * r ∧
      p ^ a * s * r ≤ M ∧ r < p ^ a ∧ (Real.log ((p ^ a : ℕ) : ℝ)) ^ 4 / 4 ≤ r ∧
      (r : ℝ) ≤ 3 * (Real.log ((p ^ a : ℕ) : ℝ)) ^ 4 :=
    fun r hr => hR r (hTR hr)
  have hpsr : ∀ r ∈ TR, ¬ p ∣ s * r := by
    intro r hr hdvd
    obtain ⟨hrp, -, hrne, -⟩ := hTR' r hr
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact hps h
    · exact hrne ((Nat.prime_dvd_prime_iff_eq hp hrp).1 h).symm
  have hsr0 : ∀ r ∈ TR, s * r ≠ 0 := fun r hr => mul_ne_zero hs0.ne' (hTR' r hr).1.ne_zero
  have hsr_smooth : ∀ r ∈ TR, PPSmooth (p ^ a - 1) (s * r) := by
    intro r hr
    obtain ⟨hrp, hrs, -, -, -, hrlt, -⟩ := hTR' r hr
    apply ppSmooth_mul_of_coprime (hsy.mono (by omega)) (ppSmooth_prime hrp (by omega))
      hs0.ne' hrp.ne_zero
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hrp).2 hrs)
  have hm_smooth : ∀ r ∈ TR, PPSmooth (p ^ a) (p ^ a * s * r) := by
    intro r hr
    rw [mul_assoc]
    exact ppSmooth_mul_of_coprime (ppSmooth_primePow hp le_rfl)
      ((hsr_smooth r hr).mono (Nat.sub_le _ _)) (pow_ne_zero _ hp.ne_zero) (hsr0 r hr)
      (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 (hpsr r hr)))
  have hm_ns : ∀ r ∈ TR, ¬ PPSmooth (p ^ a - 1) (p ^ a * s * r) := by
    intro r hr
    rw [mul_assoc]
    exact not_ppSmooth_primePow_mul hp ha (hsr0 r hr) (hpsr r hr)
  -- the removed set `T`
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = TR.image (fun r => p ^ a * s * r) := ⟨_, rfl⟩
  have hTsub : T ⊆ Ioc N M \ D := by
    intro m hm
    rw [hT, Finset.mem_image] at hm
    obtain ⟨r, hr, rfl⟩ := hm
    obtain ⟨-, -, -, hr1, hr2, -⟩ := hTR' r hr
    rw [Finset.mem_sdiff, Finset.mem_Ioc]
    exact ⟨⟨hr1, hr2⟩, fun hmD => hDns _ hmD (hm_smooth r hr)⟩
  have hinj : Set.InjOn (fun r => p ^ a * s * r) TR := by
    intro r₁ _ r₂ _ h
    have hpa : 0 < p ^ a * s := Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hs0.ne')
    exact Nat.eq_of_mul_eq_mul_left hpa h
  have hrecipT : recipSum T = ∑ r ∈ TR, (1 : ℚ) / ((p : ℚ) ^ a * s * r) := by
    rw [hT, recipSum, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Nat.cast_mul, Nat.cast_pow]
  have hdisj : Disjoint D T := Finset.disjoint_of_subset_right hTsub Finset.disjoint_sdiff
  have hnew : recipSum (Ioc N M \ (D ∪ T)) = x - ∑ r ∈ TR, (1 : ℚ) / ((p : ℚ) ^ a * s * r) := by
    have hset : Ioc N M \ (D ∪ T) = (Ioc N M \ D) \ T := by
      ext m
      simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
      tauto
    rw [hset, recipSum_sdiff hTsub, hrecipT, hx]
  -- the new denominator
  have hdvd := den_sub_sum_dvd hp ha hden hv' hs0 hps
    (fun r hr => ⟨(hTR' r hr).1, (hTR' r hr).2.2.1⟩) hTsum
  have hv'0 : v' ≠ 0 := by
    intro h; rw [h, mul_zero] at hden; exact hden0 hden
  have h0 : 0 ∉ insert v' (TR.image (s * ·)) := by
    intro h0
    rw [Finset.mem_insert, Finset.mem_image] at h0
    rcases h0 with h | ⟨r, hr, h⟩
    · exact hv'0 h.symm
    · exact hsr0 r hr h
  have hlcm_smooth : PPSmooth (p ^ a - 1) ((insert v' (TR.image (s * ·))).lcm id) := by
    apply ppSmooth_lcm _ h0
    intro n hn
    rw [Finset.mem_insert, Finset.mem_image] at hn
    rcases hn with rfl | ⟨r, hr, rfl⟩
    · apply ppSmooth_sub_one_of_not_dvd hp _ hv'
      exact hsm.of_dvd hden0 (by rw [hden]; exact dvd_mul_left _ _)
    · exact hsr_smooth r hr
  have hlcm0 : (insert v' (TR.image (s * ·))).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]; simpa using h0
  -- the mass of `T`
  have hTmass : (recipSum T : ℝ) ≤ B := by
    have h1 := recipSum_le_card_div hN0 (S := T)
      (fun m hm => (Finset.mem_Ioc.1 (Finset.mem_sdiff.1 (hTsub hm)).1).1)
    have h2 : (T.card : ℝ) ≤ R.card := by
      have : T.card ≤ R.card := by
        rw [hT]; exact Finset.card_image_le.trans (Finset.card_le_card hTR)
      exact_mod_cast this
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [hB]
    calc (recipSum T : ℝ) ≤ T.card / N := h1
      _ ≤ R.card / N := by gcongr
      _ ≤ 3 * Real.log N ^ 4 / N := by gcongr
  have hcard : (((Ioc (p ^ a) Q).filter IsPrimePow).card : ℝ) + 1 ≤
      ((Ioc (p ^ a - 1) Q).filter IsPrimePow).card := by
    have hsub : insert (p ^ a) ((Ioc (p ^ a) Q).filter IsPrimePow) ⊆
        (Ioc (p ^ a - 1) Q).filter IsPrimePow := by
      intro m hm
      rw [Finset.mem_insert] at hm
      rcases hm with rfl | hm
      · rw [Finset.mem_filter, Finset.mem_Ioc]
        have := Nat.one_le_pow a p hp.pos
        refine ⟨⟨by omega, htQ⟩, ?_⟩
        exact (isPrimePow_nat_iff _).2 ⟨p, a, hp, ha, rfl⟩
      · rw [Finset.mem_filter, Finset.mem_Ioc] at hm ⊢
        exact ⟨⟨by omega, hm.1.2⟩, hm.2⟩
    have hnotin : p ^ a ∉ (Ioc (p ^ a) Q).filter IsPrimePow := by
      intro h
      rw [Finset.mem_filter, Finset.mem_Ioc] at h
      exact lt_irrefl _ h.1.1
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnotin] at this
    exact_mod_cast this
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨D ∪ T, hD0.trans Finset.subset_union_left,
    Finset.union_subset hDI (hTsub.trans Finset.sdiff_subset), ?_, ?_, ?_⟩
  · intro n hn
    rw [Finset.mem_union] at hn
    rcases hn with hn | hn
    · exact fun h => hDns n hn (h.mono (Nat.sub_le _ _))
    · rw [hT, Finset.mem_image] at hn
      obtain ⟨r, hr, rfl⟩ := hn
      exact hm_ns r hr
  · rw [hnew]
    exact hlcm_smooth.of_dvd hlcm0 hdvd
  · rw [recipSum_union hdisj]
    push_cast
    linarith [mul_le_mul_of_nonneg_right hcard hB0]

/-! ## Asymptotic bookkeeping -/

lemma eventually_L_conds (x₀ : ℝ) : ∀ᶠ L : ℝ in atTop,
    1 ≤ L ∧ x₀ ≤ L ^ 4 / 4 ∧ 2 ≤ L ^ 4 / 4 ∧
    L ^ (39 / 10 : ℝ) ≤ L ^ 4 / (80 * Real.log L) - 18 * L - 1 := by
  have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).bound
    (by norm_num : (0 : ℝ) < 1 / 320)
  filter_upwards [h1, eventually_ge_atTop (4 * |x₀| + 8)] with L hL hL'
  have hx0 : x₀ ≤ |x₀| := le_abs_self x₀
  have habs : 0 ≤ |x₀| := abs_nonneg x₀
  have hL8 : 8 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hL4 : L ≤ L ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have hu : 0 < L ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hv : 0 < L ^ (39 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have huv : L ^ (1 / 10 : ℝ) * L ^ (39 / 10 : ℝ) = L ^ 4 := by
    rw [← Real.rpow_add hL0, show (1 / 10 : ℝ) + 39 / 10 = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hlog' : Real.log L ≤ L ^ (1 / 10 : ℝ) / 320 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogL, abs_of_pos hu] at hL
    linarith
  have hv3 : L ^ 3 ≤ L ^ (39 / 10 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ L by linarith)
      (show ((3 : ℕ) : ℝ) ≤ 39 / 10 by norm_num)
    rwa [Real.rpow_natCast] at this
  have hL3 : 9 * L ≤ L ^ 3 := by
    have : L ^ 3 = L * L ^ 2 := by ring
    nlinarith
  have key : 4 * L ^ (39 / 10 : ℝ) ≤ L ^ 4 / (80 * Real.log L) := by
    rw [le_div_iff₀ (by positivity), ← huv]
    nlinarith [mul_le_mul_of_nonneg_left hlog' hv.le]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma eventually_three_log_pow_lt : ∀ᶠ x : ℝ in atTop, 3 * Real.log x ^ 4 < x := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound (show (0 : ℝ) < 1 / 4 by norm_num)
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  simp only [id, Real.norm_eq_abs] at hx
  rw [abs_of_nonneg (by positivity), abs_of_pos hx0] at hx
  linarith

lemma eventually_t_conds (x₀ : ℝ) : ∀ᶠ t : ℕ in atTop,
    4 ≤ t ∧ 3 * Real.log t ^ 4 < t ∧ 1 ≤ Real.log t ∧ x₀ ≤ Real.log t ^ 4 / 4 ∧
    2 ≤ Real.log t ^ 4 / 4 ∧
    Real.log t ^ (39 / 10 : ℝ) ≤
      Real.log t ^ 4 / (80 * Real.log (Real.log t)) - 18 * Real.log t - 1 := by
  have hlog : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_L_conds x₀),
    tendsto_natCast_atTop_atTop.eventually eventually_three_log_pow_lt,
    eventually_ge_atTop 4] with t h1 h2 h3
  exact ⟨h3, h2, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2⟩

lemma tendsto_div_log_pow_four : Tendsto (fun x : ℝ => x / Real.log x ^ 4) atTop atTop := by
  have h : Tendsto (fun x : ℝ => Real.log x ^ 4 / x) atTop (nhds 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x ^ 4 / x := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have := Real.log_pos hx
    positivity
  have h' : Tendsto (fun x : ℝ => Real.log x ^ 4 / x) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨h, hpos⟩
  exact h'.inv_tendsto_nhdsGT_zero.congr (fun x => by simp [inv_div])

lemma eventually_N_conds (ε x₀ x₁ : ℝ) (y₀ T₀ : ℕ) : ∀ᶠ N : ℕ in atTop,
    12 ≤ N ∧ x₀ ≤ (N : ℝ) ∧ x₁ ≤ (N : ℝ) ∧ 48 / ε ≤ Real.log N ∧
    x₁ ≤ (N : ℝ) / Real.log N ^ 4 ∧ 24 / ε ≤ Real.log ((N : ℝ) / Real.log N ^ 4) ∧
    y₀ ≤ ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ ∧ T₀ ≤ ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ ∧
    10 ≤ ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx : Tendsto (fun N : ℕ => (N : ℝ) / Real.log N ^ 4) atTop atTop :=
    tendsto_div_log_pow_four.comp hN
  have hy : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp hN)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp hN
  filter_upwards [eventually_ge_atTop 12, hN.eventually_ge_atTop x₀, hN.eventually_ge_atTop x₁,
    hlog.eventually_ge_atTop (48 / ε), hx.eventually_ge_atTop x₁,
    (Real.tendsto_log_atTop.comp hx).eventually_ge_atTop (24 / ε),
    hy.eventually_ge_atTop y₀, hy.eventually_ge_atTop T₀, hy.eventually_ge_atTop 10]
    with N h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end P1

/-! ## Proposition 1 -/

open P1 in
theorem prop1 (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ M : ℕ,
    Real.exp 1 * N ≤ M → (M : ℝ) ≤ Real.exp 1 * N + 3 →
    ∃ D ⊆ Ioc N M, (recipSum D : ℝ) ≤ ε ∧ 1 / (20 * Real.log N) ≤ (recipSum D : ℝ) ∧
      PPSmooth ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ (recipSum (Ioc N M \ D)).den := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 eventually_card_primes_Ioc_ge
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 eventually_card_primePow_le
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 exists_ppSmooth_coprime
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((eventually_t_conds x₀).and lemma1)
  have hS := (tendsto_order.1 tendsto_sum_inv_primePow_Ioc).2 (ε / 8) (by positivity)
  filter_upwards [hS, eventually_N_conds ε x₀ x₁ y₀ T₀] with N hSN hN
  obtain ⟨hN12, hNx₀, hNx₁, hlogN, hxx₁, hlogx, hyy₀, hyT₀, hy10⟩ := hN
  intro M hM1 hM2
  have he1 : (27 / 10 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he2 : Real.exp 1 < 68 / 25 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hN0 : 0 < N := by omega
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN12
  have hM27 : (27 / 10 : ℝ) * N ≤ M :=
    le_trans (mul_le_mul_of_nonneg_right he1.le (Nat.cast_nonneg N)) hM1
  have hM3 : (M : ℝ) ≤ 3 * N := by
    have := mul_le_mul_of_nonneg_right he2.le (Nat.cast_nonneg (α := ℝ) N)
    linarith
  have hM3' : M ≤ 3 * N := by exact_mod_cast hM3
  have hNM : N ≤ M := by
    have : (N : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hlogN1 : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith
  have hlogN0 : 0 < Real.log N := by linarith
  have hlogN4 : 1 ≤ Real.log N ^ 4 := one_le_pow₀ hlogN1.le
  -- names for the main parameters
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, ⌊(N : ℝ) / Real.log N ^ 4⌋₊ = Q := ⟨_, rfl⟩
  rw [hQ] at hSN
  have hNy : (N : ℝ) < ((⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ : ℕ) + 1 : ℝ) ^ 12 := by
    have h1 := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 12 : ℝ))
    have h2 := pow_lt_pow_left₀ h1 (by positivity) (by norm_num : (12 : ℕ) ≠ 0)
    rwa [← Real.rpow_natCast ((N : ℝ) ^ (1 / 12 : ℝ)) 12, ← Real.rpow_mul (Nat.cast_nonneg N),
      show (1 / 12 : ℝ) * ((12 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one] at h2
  obtain ⟨y₁, hy₁⟩ : ∃ y : ℕ, ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ = y := ⟨_, rfl⟩
  rw [hy₁] at hyy₀ hyT₀ hy10 hNy ⊢
  have hy10' : (10 : ℝ) ≤ y₁ := by exact_mod_cast hy10
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 3 * Real.log N ^ 4 / N := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hQN : Q ≤ N := by
    rw [← hQ]
    exact Nat.floor_le_of_le (div_le_self (Nat.cast_nonneg _) hlogN4)
  -- the elimination procedure
  have hstep : ∀ t D, y₁ < t → t ≤ Q → ClearInv N M Q (bigPP N M Q) B t D →
      ∃ D', ClearInv N M Q (bigPP N M Q) B (t - 1) D' := by
    intro t D hyt htQ hInv
    by_cases hsm : PPSmooth (t - 1) (recipSum (Ioc N M \ D)).den
    · exact ⟨D, clearInv_sub_one hB0 hInv hsm⟩
    · obtain ⟨hconds, hL1⟩ := hT₀ t (by omega)
      have htN : (t : ℝ) ≤ N / Real.log N ^ 4 := by
        have : (t : ℝ) ≤ Q := by exact_mod_cast htQ
        rw [← hQ] at this
        exact this.trans (Nat.floor_le (by positivity))
      have hNt : Real.log N ≤ 12 * Real.log t := by
        have h1 : (N : ℝ) ^ (1 / 12 : ℝ) < t := by
          have := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 12 : ℝ))
          rw [hy₁] at this
          have h2 : (y₁ : ℝ) + 1 ≤ t := by exact_mod_cast hyt
          linarith
        have h2 := Real.log_lt_log (by positivity) h1
        rw [Real.log_rpow (by positivity)] at h2
        linarith
      exact step_main hx₀ (hy₀ y₁ hyy₀) hy10' hNy hL1 hB hN0 hM27 htN hNt hlogN1 hyt htQ
        hconds hInv hsm
  obtain ⟨D, hD⟩ := clear_all hstep clearInv_base
  obtain ⟨hD0, hDI, -, hDsm, hDmass⟩ := hD
  refine ⟨D, hDI, ?_, ?_, hDsm.mono (by omega)⟩
  · -- the upper bound `H(D) ≤ ε`
    have hD0up := recipSum_bigPP_le (Q := Q) hN0 hNM hM3'
    have hlog3N : Real.log N ≤ Real.log (3 * N) :=
      Real.log_le_log (by positivity) (by linarith)
    have hPPset : (((Ioc Q (3 * N)).filter IsPrimePow).card : ℝ) ≤
        4 * (3 * N) / Real.log (3 * N) := by
      have h1 := hx₁ ((3 * N : ℕ) : ℝ) (by push_cast; linarith)
      rw [Nat.floor_natCast] at h1
      have h2 : ((Ioc Q (3 * N)).filter IsPrimePow).card ≤
          ((Icc 1 (3 * N)).filter IsPrimePow).card := by
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        intro m hm
        rw [Finset.mem_Ioc] at hm
        rw [Finset.mem_Icc]
        omega
      calc (((Ioc Q (3 * N)).filter IsPrimePow).card : ℝ)
          ≤ (((Icc 1 (3 * N)).filter IsPrimePow).card : ℝ) := by exact_mod_cast h2
        _ ≤ 4 * (3 * N) / Real.log (3 * N) := by push_cast at h1; exact h1
    have hεN : 48 ≤ Real.log N * ε := (div_le_iff₀ hε).1 hlogN
    have hPPN : (((Ioc Q (3 * N)).filter IsPrimePow).card : ℝ) / N ≤ ε / 4 := by
      have hl3 : 0 < Real.log (3 * N) := by linarith
      have hNr0 : (0 : ℝ) < N := by positivity
      rw [div_le_iff₀ hNr0]
      calc (((Ioc Q (3 * N)).filter IsPrimePow).card : ℝ) ≤ 4 * (3 * N) / Real.log (3 * N) :=
            hPPset
        _ ≤ ε / 4 * N := by
            rw [div_le_iff₀ hl3]
            nlinarith [mul_le_mul_of_nonneg_left hlog3N hε.le]
    have hbig : (recipSum (bigPP N M Q) : ℝ) ≤ ε / 2 := by linarith
    have hcardQ : (((Icc 1 Q).filter IsPrimePow).card : ℝ) ≤
        4 * ((N : ℝ) / Real.log N ^ 4) / Real.log ((N : ℝ) / Real.log N ^ 4) := by
      have := hx₁ ((N : ℝ) / Real.log N ^ 4) hxx₁
      rwa [hQ] at this
    have hcardk : (((Ioc (Q - (Q - y₁)) Q).filter IsPrimePow).card : ℝ) ≤
        ((Icc 1 Q).filter IsPrimePow).card := by
      have : ((Ioc (Q - (Q - y₁)) Q).filter IsPrimePow).card ≤
          ((Icc 1 Q).filter IsPrimePow).card := by
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        intro m hm
        rw [Finset.mem_Ioc] at hm
        rw [Finset.mem_Icc]
        omega
      exact_mod_cast this
    have hlogx0 : 0 < Real.log ((N : ℝ) / Real.log N ^ 4) := by
      have : 0 < 24 / ε := by positivity
      linarith
    have hkey : 4 * ((N : ℝ) / Real.log N ^ 4) / Real.log ((N : ℝ) / Real.log N ^ 4) * B ≤
        ε / 2 := by
      have hNr0 : (N : ℝ) ≠ 0 := by positivity
      have hl0 : Real.log N ^ 4 ≠ 0 := by positivity
      have hlx : Real.log ((N : ℝ) / Real.log N ^ 4) ≠ 0 := hlogx0.ne'
      have h24 : 24 ≤ Real.log ((N : ℝ) / Real.log N ^ 4) * ε := (div_le_iff₀ hε).1 hlogx
      calc 4 * ((N : ℝ) / Real.log N ^ 4) / Real.log ((N : ℝ) / Real.log N ^ 4) * B
          = 12 / Real.log ((N : ℝ) / Real.log N ^ 4) := by
            rw [hB]; field_simp; ring
        _ ≤ ε / 2 := by
            rw [div_le_iff₀ hlogx0]
            linarith
    have hfin : (((Ioc (Q - (Q - y₁)) Q).filter IsPrimePow).card : ℝ) * B ≤ ε / 2 :=
      (mul_le_mul_of_nonneg_right (hcardk.trans hcardQ) hB0).trans hkey
    linarith
  · -- the lower bound
    have hlow := recipSum_bigPP_ge (M := M) (Q := Q) hN0 hlogN0 hQN hM27 hM3 (hx₀ N hNx₀)
    have hmono : (recipSum (bigPP N M Q) : ℝ) ≤ recipSum D := by
      exact_mod_cast recipSum_mono hD0
    have : 1 / (20 * Real.log N) ≤ 1 / (15 * Real.log N) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith

end Croot
