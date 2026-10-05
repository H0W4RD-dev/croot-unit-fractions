import Croot.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# The algebraic core of Croot's prime-power elimination step

Let `q = p ^ a` be a prime power and `x` a rational whose reduced denominator is `q * v'`
with `p ∤ v'`.  If `s` is coprime to `p` and `R'` is a set of primes different from `p` with
`∑_{r ∈ R'} r⁻¹ ≡ x.num · v'⁻¹ · s (mod q)`, then the reduced denominator of
`x - ∑_{r ∈ R'} 1/(q s r)` divides `lcm (v', s r : r ∈ R')`; in particular `p` no longer
appears in it.
-/

namespace Croot

open Finset

/-- If `x * L` is an integer divisible by `q` (with `L, q > 0`), then `(x / q).den ∣ L`. -/
lemma den_div_dvd_of_mul_eq {x : ℚ} {L q : ℕ} (hL : 0 < L) (hq : 0 < q) {W : ℤ}
    (hW : x * L = W) (hqW : (q : ℤ) ∣ W) : (x / q).den ∣ L := by
  obtain ⟨W', rfl⟩ := hqW
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hx : x / q = (W' : ℚ) / (L : ℤ) := by
    have : x = ((q : ℤ) * W' : ℤ) / (L : ℚ) := by
      field_simp
      exact_mod_cast hW
    rw [this]
    push_cast
    field_simp
  have h := Rat.den_dvd W' (L : ℤ)
  rw [Rat.divInt_eq_div] at h
  rw [hx]
  exact_mod_cast h

/-- Algebraic elimination step. -/
theorem den_sub_sum_dvd {p a : ℕ} (hp : p.Prime) (_ha : 0 < a) {x : ℚ} {v' : ℕ}
    (hden : x.den = p ^ a * v') (hv' : ¬ p ∣ v') {s : ℕ} (hs : 0 < s) (hps : ¬ p ∣ s)
    {R' : Finset ℕ} (hR' : ∀ r ∈ R', r.Prime ∧ r ≠ p)
    (hsum : ∑ r ∈ R', ((r : ZMod (p ^ a)))⁻¹ =
      (x.num : ZMod (p ^ a)) * ((v' : ZMod (p ^ a)))⁻¹ * (s : ZMod (p ^ a))) :
    (x - ∑ r ∈ R', (1 : ℚ) / (p ^ a * s * r)).den ∣ (insert v' (R'.image (s * ·))).lcm id := by
  set q := p ^ a with hqdef
  set L := (insert v' (R'.image (s * ·))).lcm id with hLdef
  have hq0 : 0 < q := pow_pos hp.pos a
  have hv'0 : 0 < v' := by
    rcases Nat.eq_zero_or_pos v' with h | h
    · exfalso; have := x.den_pos; rw [hden, h, mul_zero] at this; exact lt_irrefl 0 this
    · exact h
  have hr0 : ∀ r ∈ R', 0 < r := fun r hr => (hR' r hr).1.pos
  have h0notin : 0 ∉ insert v' (R'.image (s * ·)) := by
    simp only [Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
    exact ⟨hv'0.ne, fun r hr h => Nat.mul_ne_zero hs.ne' (hr0 r hr).ne' h⟩
  have hL0 : 0 < L := by
    apply Nat.pos_of_ne_zero
    rw [hLdef, Ne, Finset.lcm_eq_zero_iff]
    simpa using h0notin
  -- divisibility facts
  have hv'L : v' ∣ L := Finset.dvd_lcm (Finset.mem_insert_self _ _)
  have hsrL : ∀ r ∈ R', s * r ∣ L := fun r hr =>
    Finset.dvd_lcm (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hr))
  -- coprimality with q
  have hcop_v' : Nat.Coprime v' q := by
    rw [hqdef]; exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hv').symm
  have hcop_s : Nat.Coprime s q := by
    rw [hqdef]; exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hps).symm
  have hcop_r : ∀ r ∈ R', Nat.Coprime r q := by
    intro r hr
    rw [hqdef]
    refine Nat.Coprime.pow_right _ ?_
    exact (Nat.coprime_primes (hR' r hr).1 hp).2 (hR' r hr).2
  -- the integer W := (q x - ∑ 1/(s r)) * L
  set W : ℤ := x.num * ((L / v' : ℕ) : ℤ) - ∑ r ∈ R', ((L / (s * r) : ℕ) : ℤ) with hWdef
  have hqx : (q : ℚ) * x = (x.num : ℚ) / v' := by
    have hx : (x.num : ℚ) / (x.den : ℚ) = x := Rat.num_div_den x
    have hden' : (x.den : ℚ) = (q : ℚ) * v' := by exact_mod_cast hden
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
    have hv : (v' : ℚ) ≠ 0 := by exact_mod_cast hv'0.ne'
    conv_lhs => rw [← hx]
    rw [hden']
    field_simp
  have hmain : (q * (x - ∑ r ∈ R', (1 : ℚ) / (p ^ a * s * r))) * L = W := by
    rw [hWdef]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
    rw [mul_sub, hqx, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · rw [Nat.cast_div hv'L (by exact_mod_cast hv'0.ne')]
      field_simp
    · refine Finset.sum_congr rfl fun r hr => ?_
      rw [Nat.cast_div (hsrL r hr) (by
        have := Nat.mul_ne_zero hs.ne' (hr0 r hr).ne'
        exact_mod_cast this)]
      have hq' : (q : ℚ) = (p : ℚ) ^ a := by rw [hqdef]; push_cast; ring
      rw [hq']
      have hpa : ((p : ℚ) ^ a) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
      have hsr : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
      have hrr : (r : ℚ) ≠ 0 := by exact_mod_cast (hr0 r hr).ne'
      push_cast
      field_simp
  -- q divides W, computed in ZMod q
  have hqW : (q : ℤ) ∣ W := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hv'u : (v' : ZMod q) * (v' : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one v' hcop_v'
    have hsu : (s : ZMod q) * (s : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one s hcop_s
    have hru : ∀ r ∈ R', (r : ZMod q) * (r : ZMod q)⁻¹ = 1 :=
      fun r hr => ZMod.coe_mul_inv_eq_one r (hcop_r r hr)
    -- L / v' ≡ L * v'⁻¹ and L / (s r) ≡ L * s⁻¹ * r⁻¹
    have hLv : ((L / v' : ℕ) : ZMod q) = (L : ZMod q) * (v' : ZMod q)⁻¹ := by
      have h1 : (v' : ZMod q) * ((L / v' : ℕ) : ZMod q) = (L : ZMod q) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hv'L]
      calc ((L / v' : ℕ) : ZMod q) = ((v' : ZMod q)⁻¹ * (v' : ZMod q)) * ((L / v' : ℕ) : ZMod q) := by
            rw [mul_comm ((v' : ZMod q)⁻¹), hv'u, one_mul]
        _ = (L : ZMod q) * (v' : ZMod q)⁻¹ := by rw [mul_assoc, h1, mul_comm]
    have hLsr : ∀ r ∈ R', ((L / (s * r) : ℕ) : ZMod q) =
        (L : ZMod q) * (s : ZMod q)⁻¹ * (r : ZMod q)⁻¹ := by
      intro r hr
      have h1 : (s : ZMod q) * (r : ZMod q) * ((L / (s * r) : ℕ) : ZMod q) = (L : ZMod q) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (hsrL r hr)]
      calc ((L / (s * r) : ℕ) : ZMod q)
          = ((s : ZMod q)⁻¹ * (r : ZMod q)⁻¹ * ((s : ZMod q) * (r : ZMod q))) *
              ((L / (s * r) : ℕ) : ZMod q) := by
            rw [show (s : ZMod q)⁻¹ * (r : ZMod q)⁻¹ * ((s : ZMod q) * (r : ZMod q)) =
                ((s : ZMod q) * (s : ZMod q)⁻¹) * ((r : ZMod q) * (r : ZMod q)⁻¹) by ring,
              hsu, hru r hr, one_mul, one_mul]
        _ = (L : ZMod q) * (s : ZMod q)⁻¹ * (r : ZMod q)⁻¹ := by
            rw [mul_assoc, h1]; ring
    rw [hWdef]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
    rw [hLv, Finset.sum_congr rfl hLsr]
    rw [show ∑ x ∈ R', (L : ZMod q) * (s : ZMod q)⁻¹ * (x : ZMod q)⁻¹ =
        (L : ZMod q) * (s : ZMod q)⁻¹ * ∑ x ∈ R', (x : ZMod q)⁻¹ by rw [Finset.mul_sum], hsum]
    have : (L : ZMod q) * (s : ZMod q)⁻¹ * ((x.num : ZMod q) * (v' : ZMod q)⁻¹ * (s : ZMod q)) =
        (L : ZMod q) * (v' : ZMod q)⁻¹ * (x.num : ZMod q) * ((s : ZMod q) * (s : ZMod q)⁻¹) := by
      ring
    rw [this, hsu]
    ring
  -- conclude
  have hfinal := den_div_dvd_of_mul_eq (x := q * (x - ∑ r ∈ R', (1 : ℚ) / (p ^ a * s * r)))
    hL0 hq0 hmain hqW
  have hq0' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
  rwa [mul_div_cancel_left₀ _ hq0'] at hfinal

end Croot
