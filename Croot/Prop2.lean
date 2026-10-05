import Croot.Basic
import Croot.Primes
import Croot.Fourier
import Croot.SmoothDensity
import Croot.Core
import Croot.Asymptotics

/-!
# Croot's Proposition 2: exact representation by smooth numbers in a short interval

For fixed `η ∈ (0, 1]` there is `c > 0` such that for all large `M`, every rational
`x ∈ [M^{-1/21}, c]` whose reduced denominator is `⌊M^{1/5}⌋`-pp-smooth is a sum of
reciprocals of distinct integers in `(M, (1 + η) M]`.

Proof: build `Ỹ = Core ∪ Fill` of `⌊M^{1/5}⌋`-pp-smooth integers in `(M, (1+η)M]` with
`2x ≤ H(Ỹ) < 2x + 1/M`, and show by finite Fourier analysis modulo `P = lcm(1..y)` that some
subset `Z ⊆ Ỹ` has `H(Z) = x`.
-/

namespace Croot

open Real Finset Filter

/-! ## Greedy filling -/

/-- Greedy filling: adding elements `> M` one at a time we can land in `[T, T + 1/M)`. -/
lemma greedy_fill (M : ℕ) (F0 : Finset ℕ) (hF0 : ∀ m ∈ F0, M < m) (b T : ℚ)
    (hb : b ≤ T) (htot : T ≤ b + recipSum F0) :
    ∃ F ⊆ F0, T ≤ b + recipSum F ∧ b + recipSum F < T + 1 / ((M : ℚ) + 1) := by
  induction F0 using Finset.induction_on with
  | empty =>
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · simpa using htot
    · simp only [recipSum_empty, add_zero]
      have : (0 : ℚ) < 1 / ((M : ℚ) + 1) := by positivity
      linarith
  | insert a F0 ha ih =>
    have hF0' : ∀ m ∈ F0, M < m := fun m hm => hF0 m (Finset.mem_insert_of_mem hm)
    have haM : M < a := hF0 a (Finset.mem_insert_self a F0)
    have hins : recipSum (insert a F0) = 1 / (a : ℚ) + recipSum F0 := by
      simp [recipSum, Finset.sum_insert ha]
    by_cases hT : T ≤ b + recipSum F0
    · obtain ⟨F, hF, h1, h2⟩ := ih hF0' hT
      exact ⟨F, hF.trans (Finset.subset_insert _ _), h1, h2⟩
    · push Not at hT
      refine ⟨insert a F0, le_rfl, ?_, ?_⟩
      · rw [hins] at htot ⊢; linarith
      · rw [hins]
        have ha1 : (1 : ℚ) / a ≤ 1 / ((M : ℚ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast haM
        linarith

/-! ## Small auxiliary facts -/

lemma abs_le_of_mem_window {P : ℕ} {h : ℤ} (hh : h ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ))
    (-((P / 2 : ℕ) : ℤ) + P)) : |(h : ℝ)| ≤ (P : ℝ) / 2 := by
  rw [Finset.mem_Ico] at hh
  obtain ⟨h1, h2⟩ := hh
  have hP2 : ((P / 2 : ℕ) : ℝ) ≤ (P : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self P 2
  have hP2' : (P : ℝ) - ((P / 2 : ℕ) : ℝ) ≤ (P : ℝ) / 2 + 1 / 2 := by
    have : (P : ℝ) ≤ 2 * ((P / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show P ≤ 2 * (P / 2) + 1 by omega)
    linarith
  have h1' : -((P / 2 : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast h1
  have h2' : (h : ℝ) + 1 ≤ -((P / 2 : ℕ) : ℝ) + P := by
    have : h + 1 ≤ -((P / 2 : ℕ) : ℤ) + P := h2
    exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith

lemma zero_mem_window {P : ℕ} (hP : 0 < P) :
    (0 : ℤ) ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P) := by
  rw [Finset.mem_Ico]
  have : P / 2 < P := Nat.div_lt_self hP (by norm_num)
  constructor <;> omega

lemma card_window (P : ℕ) :
    (Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).card = P := by
  rw [Int.card_Ico]
  simp

/-- A set of integers `> M` has reciprocal sum at most `#S / M`. -/
lemma recipSum_le_card_div {S : Finset ℕ} {M : ℕ} (hM : 0 < M) (h : ∀ m ∈ S, M < m) :
    ((recipSum S : ℚ) : ℝ) ≤ S.card / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [recipSum, Rat.cast_sum]
  calc ∑ n ∈ S, (((1 : ℚ) / n : ℚ) : ℝ) ≤ ∑ _n ∈ S, (1 : ℝ) / M := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' : (M : ℝ) ≤ n := by exact_mod_cast (h n hn).le
        push_cast
        exact one_div_le_one_div_of_le hM' hn'
    _ = S.card / M := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- If a finite sum of complex numbers equals `P * c` with `c` a natural number and the sum of
the real parts is positive, then `c > 0`. -/
lemma pos_of_sum_eq_mul {ι : Type*} (s : Finset ι) (f : ι → ℂ) (P c : ℕ)
    (h : ∑ i ∈ s, f i = (P : ℂ) * (c : ℂ)) (hpos : 0 < ∑ i ∈ s, (f i).re) : 0 < c := by
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have h3 : ((P : ℂ) * (c : ℂ)).re = (P : ℝ) * c := by simp
  rw [h3] at h2
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp only [Nat.cast_zero, mul_zero] at h2
    linarith
  · exact hc

/-! ## The proposition -/

set_option maxHeartbeats 2000000 in
theorem prop2 (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
    ∀ x : ℚ, (M : ℝ) ^ (-(1 / 21 : ℝ)) ≤ x → (x : ℝ) ≤ c →
      PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ x.den →
      ∃ Y ⊆ Ioc M ⌊(1 + η) * M⌋₊, recipSum Y = x := by
  set B : ℕ := ⌈16 / η⌉₊ with hBdef
  have hB : 0 < B := Nat.ceil_pos.2 (by positivity)
  obtain ⟨cG, hcG, hGcard⟩ := card_smoothRough_ge B
  obtain ⟨κ, hκ, hmass⟩ := mass_smooth_ge
  refine ⟨min (κ * η / 2) (1 / 8), lt_min (by positivity) (by norm_num), ?_⟩
  filter_upwards [core_exists η hη hη1, hGcard, hmass η hη hη1,
    prop2_eventually η hη hη1 cG hcG B hB] with M hcore hGM hmassM hev
  obtain ⟨hM0, hX2, hWM, hCAsmall, hδhalf, hPbig, hdecay, hy2⟩ := hev
  intro x hx1 hx2 hxden
  set y : ℕ := ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ with hydef
  set W : ℝ := (M : ℝ) ^ (3 / 4 : ℝ) with hWdef
  set X : ℝ := W * (Real.log M) ^ 4 with hXdef
  set P : ℕ := Nat.lcmUpto y with hPdef
  set U : ℕ := ⌊(1 + η) * M⌋₊ with hUdef
  set D : ℕ := (Nat.log 2 (2 * M) + 2) ^ 3 * B with hDdef
  set G : Finset ℕ := (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter
    (fun n => PPSmooth y n ∧ ∀ p ∈ Finset.Iic B, p.Prime → ¬ p ∣ n) with hGdef
  set Pr : Finset ℕ := (Finset.Iic y).filter Nat.Prime with hPrdef
  set Sm : Finset ℕ := (Ioc M U).filter (PPSmooth y) with hSmdef
  -- basic positivity facts
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hW0 : 0 < W := Real.rpow_pos_of_pos hMr _
  have hX0 : 0 < X := by linarith
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.rpow_pos_of_pos hMr _) hx1
  have hxc : (x : ℝ) ≤ κ * η / 2 := hx2.trans (min_le_left _ _)
  have hx8 : (x : ℝ) ≤ 1 / 8 := hx2.trans (min_le_right _ _)
  have hPpos : 0 < P := Nat.lcmUpto_pos y
  have hPr' : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hD : 0 < D := Nat.mul_pos (by positivity) hB
  have h2M : (1 + η) * (M : ℝ) ≤ 2 * M := by nlinarith
  -- the core elements
  have hcore' : ∀ n p, n ∈ G → p ∈ Pr → ∃ m : ℕ, M < m ∧ (m : ℝ) ≤ (1 + η) * M ∧
      PPSmooth y m ∧ n ∣ m ∧ p ^ Nat.log p y ∣ m ∧ m / n ∈ cofSet B m := by
    intro n p hn hp
    rw [hGdef, Finset.mem_filter, Finset.mem_Ioc] at hn
    rw [hPrdef, Finset.mem_filter, Finset.mem_Iic] at hp
    obtain ⟨⟨hn1, hn2⟩, hn3, hn4⟩ := hn
    have hXn : X < n := (Nat.floor_lt hX0.le).1 hn1
    have hn2X : (n : ℝ) ≤ 2 * X := (Nat.cast_le.2 hn2).trans (Nat.floor_le (by positivity))
    exact hcore n hXn hn2X hn3 hn4 p hp.2 hp.1
  choose! mf hmf using hcore'
  set CA : Finset ℕ := G.biUnion (fun n => Pr.image (mf n)) with hCAdef
  have hCAmem : ∀ m ∈ CA, ∃ n ∈ G, ∃ p ∈ Pr, mf n p = m := by
    intro m hm
    rw [hCAdef, Finset.mem_biUnion] at hm
    obtain ⟨n, hn, hm⟩ := hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
    exact ⟨n, hn, p, hp, rfl⟩
  have hCAprop : ∀ m ∈ CA, M < m ∧ (m : ℝ) ≤ (1 + η) * M ∧ PPSmooth y m := by
    intro m hm
    obtain ⟨n, hn, p, hp, rfl⟩ := hCAmem m hm
    obtain ⟨h1, h2, h3, -⟩ := hmf n p hn hp
    exact ⟨h1, h2, h3⟩
  have hCASm : CA ⊆ Sm := by
    intro m hm
    obtain ⟨h1, h2, h3⟩ := hCAprop m hm
    rw [hSmdef, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨h1, Nat.le_floor h2⟩, h3⟩
  have h2Pr : 2 ∈ Pr := by
    rw [hPrdef, Finset.mem_filter, Finset.mem_Iic]
    exact ⟨hy2, Nat.prime_two⟩
  have hlcm : ∀ n ∈ G, (Pr.image (mf n)).lcm id = P := by
    intro n hn
    rw [hPdef]
    apply lcm_eq_lcmUpto
    · intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
      obtain ⟨h1, -, h3, -⟩ := hmf n p hn hp
      exact ⟨lt_of_le_of_lt (Nat.zero_le _) h1, h3⟩
    · intro p hp hpy
      have hpPr : p ∈ Pr := by
        rw [hPrdef, Finset.mem_filter, Finset.mem_Iic]
        exact ⟨hpy, hp⟩
      exact ⟨mf n p, Finset.mem_image_of_mem _ hpPr, (hmf n p hn hpPr).2.2.2.2.1⟩
  -- the reciprocal mass of the core is small
  have hGle : (G.card : ℝ) ≤ 2 * X := by
    have h1 : G.card ≤ ⌊2 * X⌋₊ :=
      calc G.card ≤ (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).card := Finset.card_filter_le _ _
        _ = ⌊2 * X⌋₊ - ⌊X⌋₊ := Nat.card_Ioc _ _
        _ ≤ ⌊2 * X⌋₊ := Nat.sub_le _ _
    calc (G.card : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ 2 * X := Nat.floor_le (by positivity)
  have hPrle : (Pr.card : ℝ) ≤ (y : ℝ) + 1 := by
    have : Pr.card ≤ y + 1 :=
      calc Pr.card ≤ (Finset.Iic y).card := Finset.card_filter_le _ _
        _ = y + 1 := Nat.card_Iic y
    exact_mod_cast this
  have hCAcard : (CA.card : ℝ) ≤ (2 * X + 1) * ((y : ℝ) + 1) := by
    have h1 : CA.card ≤ G.card * Pr.card :=
      calc CA.card ≤ ∑ n ∈ G, (Pr.image (mf n)).card := Finset.card_biUnion_le
        _ ≤ ∑ _n ∈ G, Pr.card := Finset.sum_le_sum fun n _ => Finset.card_image_le
        _ = G.card * Pr.card := by rw [Finset.sum_const, smul_eq_mul]
    calc (CA.card : ℝ) ≤ (G.card : ℝ) * Pr.card := by exact_mod_cast h1
      _ ≤ (2 * X + 1) * ((y : ℝ) + 1) :=
        mul_le_mul (by linarith) hPrle (by positivity) (by positivity)
  have hCAmass : ((recipSum CA : ℚ) : ℝ) ≤ (x : ℝ) / 2 := by
    calc ((recipSum CA : ℚ) : ℝ) ≤ CA.card / M :=
          recipSum_le_card_div hM0 (fun m hm => (hCAprop m hm).1)
      _ ≤ (2 * X + 1) * ((y : ℝ) + 1) / M := div_le_div_of_nonneg_right hCAcard hMr.le
      _ ≤ (M : ℝ) ^ (-(1 / 21 : ℝ)) / 2 := hCAsmall
      _ ≤ (x : ℝ) / 2 := by linarith
  -- greedy filling with further smooth numbers
  have hSmM : ∀ m ∈ Sm, M < m ∧ m ≤ U ∧ PPSmooth y m := by
    intro m hm
    rw [hSmdef, Finset.mem_filter, Finset.mem_Ioc] at hm
    exact ⟨hm.1.1, hm.1.2, hm.2⟩
  have hb : recipSum CA ≤ 2 * x := by
    have : ((recipSum CA : ℚ) : ℝ) ≤ ((2 * x : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have htot : 2 * x ≤ recipSum CA + recipSum (Sm \ CA) := by
    rw [recipSum_sdiff hCASm]
    have : ((2 * x : ℚ) : ℝ) ≤ ((recipSum Sm : ℚ) : ℝ) := by push_cast; linarith
    have : 2 * x ≤ recipSum Sm := by exact_mod_cast this
    linarith
  obtain ⟨F, hFsub, hF1, hF2⟩ := greedy_fill M (Sm \ CA)
    (fun m hm => (hSmM m (Finset.mem_sdiff.1 hm).1).1) (recipSum CA) (2 * x) hb htot
  set Yt : Finset ℕ := CA ∪ F with hYtdef
  have hdisj : Disjoint CA F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    exact (Finset.mem_sdiff.1 (hFsub haF)).2 ha
  have hYtsum : recipSum Yt = recipSum CA + recipSum F := recipSum_union hdisj
  have hYtSm : Yt ⊆ Sm := Finset.union_subset hCASm (hFsub.trans Finset.sdiff_subset)
  have hH1 : 2 * (x : ℝ) ≤ ((recipSum Yt : ℚ) : ℝ) := by
    have : 2 * x ≤ recipSum Yt := by rw [hYtsum]; exact hF1
    exact_mod_cast this
  have hH2 : ((recipSum Yt : ℚ) : ℝ) < 2 * (x : ℝ) + 1 / ((M : ℝ) + 1) := by
    have h' : recipSum Yt < 2 * x + 1 / ((M : ℚ) + 1) := by rw [hYtsum]; exact hF2
    have h'' : ((recipSum Yt : ℚ) : ℝ) < ((2 * x + 1 / ((M : ℚ) + 1) : ℚ) : ℝ) :=
      Rat.cast_lt.2 h'
    push_cast at h''
    exact h''
  have hYtdvd : ∀ m ∈ Yt, 0 < m ∧ m ∣ P := by
    intro m hm
    obtain ⟨h1, -, h3⟩ := hSmM m (hYtSm hm)
    have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le M) h1
    exact ⟨hm0, h3.dvd_lcmUpto hm0.ne'⟩
  have hxP : ∃ z : ℤ, x * P = z := by
    have hdvd : x.den ∣ P := hxden.dvd_lcmUpto x.den_ne_zero
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨x.num * k, ?_⟩
    rw [hk]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  -- Fourier analysis
  have key := fourier_count Yt P hPpos hYtdvd x hxP (-((P / 2 : ℕ) : ℤ))
  set A : ℝ := 2 ^ Yt.card / (2 * P) with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ h ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P),
      -A ≤ (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Yt, (1 + eC ((h : ℝ) / m))).re := by
    intro h hh
    have habs : |(h : ℝ)| ≤ (P : ℝ) / 2 := abs_le_of_mem_window hh
    by_cases hsm : |(h : ℝ)| ≤ W
    · -- small frequencies: nonnegative real part
      have hnn := re_term_nonneg Yt x h (fun m hm => by
        have h1 := (hSmM m (hYtSm hm)).1
        have h1' : (M : ℝ) < m := by exact_mod_cast h1
        exact ⟨lt_of_le_of_lt (Nat.zero_le M) h1, by linarith⟩) (by
        rw [abs_mul]
        have h0 : 0 ≤ ((recipSum Yt : ℚ) : ℝ) / 2 - x := by linarith
        rw [abs_of_nonneg h0]
        have h3 : ((recipSum Yt : ℚ) : ℝ) / 2 - x ≤ 1 / (2 * ((M : ℝ) + 1)) := by
          have e : 1 / (2 * ((M : ℝ) + 1)) = (1 / ((M : ℝ) + 1)) / 2 := by field_simp
          rw [e]
          linarith
        calc |(h : ℝ)| * (((recipSum Yt : ℚ) : ℝ) / 2 - x) ≤ W * (1 / (2 * ((M : ℝ) + 1))) :=
              mul_le_mul hsm h3 h0 hW0.le
          _ ≤ 1 / 4 := by
              rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith)
      linarith
    · -- large frequencies: some factor is far from `1`, for many cores
      push Not at hsm
      have hfar : ∀ n ∈ G, ∃ m ∈ Pr.image (mf n), ∀ j : ℤ, W ≤ |(h : ℝ) - j * m| := by
        intro n hn
        have hnX : X < n := by
          have hn' := hn
          rw [hGdef, Finset.mem_filter, Finset.mem_Ioc] at hn'
          exact (Nat.floor_lt hX0.le).1 hn'.1.1
        apply exists_far (Pr.image (mf n)) n W h
        · exact ⟨mf n 2, Finset.mem_image_of_mem _ h2Pr⟩
        · intro m hm
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
          exact lt_of_le_of_lt (Nat.zero_le M) (hmf n p hn hp).1
        · intro m hm
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
          exact (hmf n p hn hp).2.2.2.1
        · exact hW0.le
        · linarith
        · exact hsm
        · rw [hlcm n hn]
          linarith
      choose! g hg using hfar
      set J : Finset ℕ := G.image g with hJdef
      have hJCA : J ⊆ CA := by
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
        exact Finset.mem_biUnion.2 ⟨n, hn, (hg n hn).1⟩
      have hJsub : J ⊆ Yt := hJCA.trans Finset.subset_union_left
      have hJcard : G.card ≤ D * J.card := by
        apply Finset.card_le_mul_card_image
        intro b hb
        obtain ⟨hbM, hbU, -⟩ := hCAprop b (hJCA hb)
        have hb0 : 0 < b := lt_of_le_of_lt (Nat.zero_le M) hbM
        have hb2 : b ≤ 2 * M := by
          have : (b : ℝ) ≤ 2 * M := by linarith
          exact_mod_cast this
        refine le_trans (Finset.card_le_card ?_) ((card_fiber_le B b hb0 G).trans ?_)
        · intro n hn
          rw [Finset.mem_filter] at hn ⊢
          obtain ⟨hnG, hgn⟩ := hn
          obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 (hg n hnG).1
          obtain ⟨-, -, -, hdvd, -, hcof⟩ := hmf n p hnG hp
          rw [hpe, hgn] at hdvd hcof
          exact ⟨hnG, hdvd, hcof⟩
        · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
            (Nat.add_le_add_right (Nat.log_mono_right hb2) 2) 3)
      set δ : ℝ := W / ((1 + η) * M) with hδdef
      have hδ0 : 0 ≤ δ := by positivity
      have hnorm := norm_term_le Yt J hJsub x h δ hδ0 hδhalf (by
        intro m hm j
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
        have hfarn := (hg n hn).2 j
        obtain ⟨hgM, hgU, -⟩ := hCAprop (g n) (hJCA (Finset.mem_image_of_mem g hn))
        have hgpos : (0 : ℝ) < g n := by
          have : (M : ℝ) < g n := by exact_mod_cast hgM
          linarith
        have hgne : (g n : ℝ) ≠ 0 := hgpos.ne'
        have e : (h : ℝ) / (g n) - j = ((h : ℝ) - j * g n) / g n := by
          rw [sub_div, mul_div_cancel_right₀ _ hgne]
        rw [e, abs_div, abs_of_pos hgpos]
        calc δ = W / ((1 + η) * M) := rfl
          _ ≤ W / g n := div_le_div_of_nonneg_left hW0.le hgpos hgU
          _ ≤ |(h : ℝ) - j * g n| / g n := div_le_div_of_nonneg_right hfarn hgpos.le)
      have hpow : (1 - 4 * δ ^ 2) ^ J.card ≤ 1 / (2 * (P : ℝ)) := by
        have hδ2 : δ * δ ≤ 1 / 2 * (1 / 2) := mul_le_mul hδhalf hδhalf hδ0 (by norm_num)
        have h1 : 0 ≤ 1 - 4 * δ ^ 2 := by nlinarith
        have h2 : 1 - 4 * δ ^ 2 ≤ Real.exp (-(4 * δ ^ 2)) := by
          have := Real.add_one_le_exp (-(4 * δ ^ 2))
          linarith
        have hJr : cG * X ≤ (D : ℝ) * J.card := by
          have : (G.card : ℝ) ≤ (D : ℝ) * J.card := by exact_mod_cast hJcard
          linarith
        have hDr : (0 : ℝ) < D := by exact_mod_cast hD
        calc (1 - 4 * δ ^ 2) ^ J.card ≤ Real.exp (-(4 * δ ^ 2)) ^ J.card :=
              pow_le_pow_left₀ h1 h2 _
          _ = Real.exp (J.card * (-(4 * δ ^ 2))) := (Real.exp_nat_mul _ _).symm
          _ ≤ Real.exp (-(4 * δ ^ 2 * (cG * X) / D)) := by
              apply Real.exp_le_exp.2
              have h3 : cG * X / D ≤ J.card := by
                rw [div_le_iff₀ hDr]
                linarith
              have h4 : 0 ≤ 4 * δ ^ 2 := by positivity
              have h5 := mul_le_mul_of_nonneg_left h3 h4
              have e : 4 * δ ^ 2 * (cG * X) / D = 4 * δ ^ 2 * (cG * X / D) := by ring
              rw [e]
              linarith
          _ ≤ 1 / (2 * P) := hdecay
      have hre := (abs_le.1 (Complex.abs_re_le_norm
        (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Yt, (1 + eC ((h : ℝ) / m))))).1
      have h2pos : (0 : ℝ) ≤ 2 ^ Yt.card := by positivity
      have h6 := mul_le_mul_of_nonneg_left hpow h2pos
      have eA : A = 2 ^ Yt.card * (1 / (2 * (P : ℝ))) := by rw [hAdef]; ring
      linarith
  have hsumpos : 0 < ∑ h ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P),
      (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Yt, (1 + eC ((h : ℝ) / m))).re := by
    rw [← Finset.add_sum_erase _ _ (zero_mem_window hPpos)]
    have h0 : (eC (-(((0 : ℤ) : ℝ) * (x : ℝ))) * ∏ m ∈ Yt, (1 + eC (((0 : ℤ) : ℝ) / m))).re
        = 2 ^ Yt.card := by
      rw [term_zero]
      rw [show (2 : ℂ) ^ Yt.card = ((2 ^ Yt.card : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_re _
    rw [h0]
    have hcard : (((Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).erase 0).card : ℝ)
        ≤ P := by
      have : ((Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).erase 0).card ≤ P := by
        calc _ ≤ (Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).card :=
              Finset.card_erase_le
          _ = P := card_window P
      exact_mod_cast this
    have hlow : -(A * P) ≤ ∑ h ∈ (Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).erase 0,
        (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Yt, (1 + eC ((h : ℝ) / m))).re := by
      calc -(A * P) ≤ -(A * ((Finset.Ico (-((P / 2 : ℕ) : ℤ))
            (-((P / 2 : ℕ) : ℤ) + P)).erase 0).card) := by
            have := mul_le_mul_of_nonneg_left hcard hA0
            linarith
        _ = ∑ _h ∈ (Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).erase 0, (-A) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ _ := Finset.sum_le_sum fun h hh => hterm h (Finset.mem_of_mem_erase hh)
    have eAP : A * P = 2 ^ Yt.card / 2 := by
      rw [hAdef]
      field_simp
    have : (0 : ℝ) < 2 ^ Yt.card := by positivity
    linarith
  have hc := pos_of_sum_eq_mul _ _ P _ key hsumpos
  obtain ⟨Z, hZ⟩ := Finset.card_pos.1 hc
  classical
  rw [Finset.mem_filter, Finset.mem_powerset] at hZ
  obtain ⟨hZsub, k, hk⟩ := hZ
  have hk0 : k = 0 := by
    have hZnn : 0 ≤ recipSum Z := recipSum_nonneg Z
    have hZle : recipSum Z ≤ recipSum Yt := recipSum_mono hZsub
    have hx8q : x ≤ 1 / 8 := by
      have : ((x : ℚ) : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) := by push_cast; exact hx8
      exact Rat.cast_le.1 this
    have hxq : 0 < x := by exact_mod_cast hxpos
    have hM1 : (1 : ℚ) / ((M : ℚ) + 1) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (1 : ℚ) ≤ M := by exact_mod_cast hM0
      linarith
    have hYtq : recipSum Yt < 2 * x + 1 / ((M : ℚ) + 1) := by rw [hYtsum]; exact hF2
    have h1 : (k : ℚ) < 1 := by rw [← hk]; linarith
    have h2 : (-1 : ℚ) < k := by rw [← hk]; linarith
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast h2
    omega
  refine ⟨Z, fun m hm => ?_, ?_⟩
  · have := hYtSm (hZsub hm)
    rw [hSmdef, Finset.mem_filter] at this
    exact this.1
  · have : recipSum Z - x = 0 := by rw [hk, hk0]; simp
    linarith

end Croot
