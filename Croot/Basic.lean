import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# Basic definitions for the formalization of Croot's theorem

* `Croot.recipSum S = ∑_{n ∈ S} 1/n` as a rational number;
* `Croot.PPSmooth y n`: every prime power exactly dividing `n` is at most `y`.
-/

open Finset

namespace Croot

/-- The sum of reciprocals of a finite set of natural numbers, as a rational number. -/
def recipSum (S : Finset ℕ) : ℚ := ∑ n ∈ S, (1 : ℚ) / n

@[simp] lemma recipSum_empty : recipSum ∅ = 0 := by simp [recipSum]

lemma recipSum_union {S T : Finset ℕ} (h : Disjoint S T) :
    recipSum (S ∪ T) = recipSum S + recipSum T := by
  simp [recipSum, sum_union h]

lemma recipSum_sdiff {S T : Finset ℕ} (h : T ⊆ S) :
    recipSum (S \ T) = recipSum S - recipSum T := by
  have := sum_sdiff (f := fun n : ℕ => (1 : ℚ) / n) h
  simp only [recipSum]
  linarith

lemma recipSum_nonneg (S : Finset ℕ) : 0 ≤ recipSum S :=
  sum_nonneg fun _ _ => by positivity

lemma recipSum_mono {S T : Finset ℕ} (h : S ⊆ T) : recipSum S ≤ recipSum T :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity

/-- `n` is `y`-prime-power-smooth: every prime power `p ^ v_p(n)` with `p ∣ n` is `≤ y`. -/
def PPSmooth (y n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ n.factorization p ≤ y

instance (y : ℕ) : DecidablePred (PPSmooth y) := fun n => by
  unfold PPSmooth; infer_instance

lemma ppSmooth_one (y : ℕ) : PPSmooth y 1 := by simp [PPSmooth]

lemma PPSmooth.mono {y y' n : ℕ} (h : PPSmooth y n) (hy : y ≤ y') : PPSmooth y' n :=
  fun p hp => (h p hp).trans hy

lemma PPSmooth.of_dvd {y n d : ℕ} (h : PPSmooth y n) (hn : n ≠ 0) (hd : d ∣ n) :
    PPSmooth y d := by
  intro p hp
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
  have hpn : p ∈ n.primeFactors := Nat.primeFactors_mono hd hn hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  calc p ^ d.factorization p ≤ p ^ n.factorization p :=
        Nat.pow_le_pow_right hpp.pos ((Nat.factorization_le_iff_dvd hd0 hn).2 hd p)
    _ ≤ y := h p hpn

/-- A `y`-pp-smooth positive integer divides `lcm(1, …, y)`. -/
lemma PPSmooth.dvd_lcmUpto {y n : ℕ} (h : PPSmooth y n) (hn : n ≠ 0) :
    n ∣ Nat.lcmUpto y := by
  rw [← Nat.factorization_le_iff_dvd hn (Nat.lcmUpto_ne_zero y)]
  intro p
  by_cases hp : p ∈ n.primeFactors
  · have hpp := Nat.prime_of_mem_primeFactors hp
    rw [Nat.factorization_lcmUpto y hpp]
    exact Nat.le_log_of_pow_le hpp.one_lt (h p hp)
  · have : n.factorization p = 0 := by
      rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
    simp [this]

/-- Divisors of `lcm(1, …, y)` are `y`-pp-smooth. -/
lemma ppSmooth_of_dvd_lcmUpto {y n : ℕ} (hn : n ∣ Nat.lcmUpto y) : PPSmooth y n := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hle : n.factorization p ≤ p.log y := by
    rw [← Nat.factorization_lcmUpto y hpp]
    exact (Nat.factorization_le_iff_dvd (Nat.ne_of_gt (Nat.pos_of_mem_primeFactors hp) |>.symm
      |> fun h => by
        intro h0; subst h0; simp at hp) (Nat.lcmUpto_ne_zero y)).2 hn p
  calc p ^ n.factorization p ≤ p ^ p.log y := Nat.pow_le_pow_right hpp.pos hle
    _ ≤ y := by
      rcases Nat.eq_zero_or_pos y with hy | hy
      · subst hy
        have : (Nat.lcmUpto 0) = 1 := by simp [Nat.lcmUpto]
        rw [this, Nat.dvd_one] at hn
        subst hn; simp at hp
      · exact Nat.pow_log_le_self p hy.ne'

/-- The least common multiple of `y`-pp-smooth numbers is `y`-pp-smooth. -/
lemma ppSmooth_lcm {y : ℕ} {S : Finset ℕ} (hS : ∀ n ∈ S, PPSmooth y n) (h0 : 0 ∉ S) :
    PPSmooth y (S.lcm id) := by
  apply ppSmooth_of_dvd_lcmUpto
  apply Finset.lcm_dvd
  intro n hn
  exact (hS n hn).dvd_lcmUpto (fun h => h0 (h ▸ hn))

/-- The reduced denominator of `∑_{n∈S} 1/n` divides `lcm S`. -/
lemma den_recipSum_dvd {S : Finset ℕ} (hS : 0 ∉ S) : (recipSum S).den ∣ S.lcm id := by
  set L := S.lcm id with hLdef
  have hL0 : L ≠ 0 := by
    rw [hLdef, Ne, Finset.lcm_eq_zero_iff]
    simpa using hS
  have key : recipSum S = (((∑ n ∈ S, L / n : ℕ) : ℤ) : ℚ) / (((L : ℕ) : ℤ) : ℚ) := by
    simp only [Int.cast_natCast]
    rw [recipSum, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (fun h : n = 0 => hS (h ▸ hn))
    have hdvd : n ∣ L := Finset.dvd_lcm hn
    rw [Nat.cast_div hdvd hn0]
    have hL : (L : ℚ) ≠ 0 := by exact_mod_cast hL0
    field_simp
  have h := Rat.den_dvd ((∑ n ∈ S, L / n : ℕ) : ℤ) ((L : ℕ) : ℤ)
  rw [Rat.divInt_eq_div] at h
  rw [key]
  exact_mod_cast h

/-- The reduced denominator of a sum of reciprocals of `y`-pp-smooth numbers is `y`-pp-smooth. -/
lemma ppSmooth_den_recipSum {y : ℕ} {S : Finset ℕ} (hS : ∀ n ∈ S, PPSmooth y n) (h0 : 0 ∉ S) :
    PPSmooth y (recipSum S).den :=
  (ppSmooth_lcm hS h0).of_dvd (by
    rw [Ne, Finset.lcm_eq_zero_iff]; simpa using h0) (den_recipSum_dvd h0)

end Croot
