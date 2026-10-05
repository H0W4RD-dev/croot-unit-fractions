import Croot.Basic
import Croot.Harmonic
import Croot.Prop1
import Croot.Prop2
import Croot.Asymptotics
import Mathlib.Order.Lattice.Nat

/-!
# Croot's theorem on unit fractions with denominators in short intervals

This file assembles the proof of the case `r = 1` of the Main Theorem of

  E. S. Croot III, *On unit fractions with denominators in short intervals*,
  Acta Arith. 99 (2001), 99–114,

and derives the answers to the questions of Erdős and Graham (Old and New Problems and Results
in Combinatorial Number Theory, 1980, p. 33; Erdős problem #286; Justin Sun Prize JSP-000243):

* `Croot.croot_upper`: for every `ε > 0` and all large `N` there are distinct integers in
  `(N, (e + ε) N]` whose reciprocals sum to `1`;
* `Croot.croot_lower`: conversely any such set inside `(N, U]` forces `U ≥ e N`;
* `Croot.tendsto_shortestEnd`: the shortest interval `(N, U]` containing distinct integers
  whose reciprocals sum to one has `U / N → e`;
* `Croot.erdos_graham_q1`, `Croot.liminf_ratio_eq_exp_one` (with `Croot.infinite_admissible_ratio_le`,
  `Croot.finite_admissible_ratio_le`): infinitely many representations `1 = ∑ 1/xᵢ`
  (`2 ≤ x₁ < ⋯ < x_k`) with `x_k / x₁` bounded, and `liminf x_k / x₁ = e`.
-/

namespace Croot

open Real Finset Filter

/-- The denominator of `1 - q` divides that of `q`. -/
lemma den_one_sub_dvd (q : ℚ) : (1 - q).den ∣ q.den := by
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have key : 1 - q = (((q.den : ℤ) - q.num : ℤ) : ℚ) / ((q.den : ℤ) : ℚ) := by
    push_cast
    rw [sub_div, div_self hq, Rat.num_div_den]
  have h := Rat.den_dvd ((q.den : ℤ) - q.num) (q.den : ℤ)
  rw [Rat.divInt_eq_div] at h
  rw [key]
  exact_mod_cast h

/-- **Croot's theorem** (the case `r = 1` of the Main Theorem of [Croot 2001], with an `o(1)`
error term): for every `ε > 0` and every sufficiently large `N` there is a finite set of
(distinct) integers in `(N, (e + ε) N]` whose reciprocals sum to `1`. -/
theorem croot_upper (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,
    ∃ X ⊆ Ioc N ⌊(Real.exp 1 + ε) * N⌋₊, recipSum X = 1 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set η : ℝ := min 1 (ε / (2 * Real.exp 1)) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηe : η * Real.exp 1 ≤ ε / 2 := by
    have h : η ≤ ε / (2 * Real.exp 1) := min_le_right _ _
    calc η * Real.exp 1 ≤ ε / (2 * Real.exp 1) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right h he.le
      _ = ε / 2 := by field_simp
  obtain ⟨c, hc, hprop2⟩ := prop2 η hη hη1
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hprop2
  filter_upwards [prop1 (c / 2) (by positivity), main_eventually, Filter.eventually_ge_atTop M₀,
    Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop ⌈12 / ε⌉₊]
    with N hP1 hmain hNM₀ hN1 hNε
  obtain ⟨M, hNM, hH1, hH2, hM1, hM2⟩ := exists_harmonic_block hN1
  obtain ⟨D, hDsub, hDmass, hDlow, hDsmooth⟩ := hP1 M hM1 hM2
  have hqeq : recipSum (Ioc N M \ D) = recipSum (Ioc N M) - recipSum D := recipSum_sdiff hDsub
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hMr : (N : ℝ) ≤ M := by exact_mod_cast hNM.le
  -- the residual `x = 1 - H((N, M] \ D)`
  have hx_le : ((1 - recipSum (Ioc N M \ D) : ℚ) : ℝ) ≤ c := by
    have h1 : 1 - recipSum (Ioc N M \ D) ≤ recipSum D := by rw [hqeq]; linarith
    have h1' : ((1 - recipSum (Ioc N M \ D) : ℚ) : ℝ) ≤ ((recipSum D : ℚ) : ℝ) := by
      exact_mod_cast h1
    linarith
  have hx_ge : (M : ℝ) ^ (-(1 / 21 : ℝ)) ≤ ((1 - recipSum (Ioc N M \ D) : ℚ) : ℝ) := by
    have h1 : recipSum D - 1 / (M : ℚ) ≤ 1 - recipSum (Ioc N M \ D) := by
      rw [hqeq]; linarith
    have h1' : ((recipSum D : ℚ) : ℝ) - 1 / (M : ℝ) ≤ ((1 - recipSum (Ioc N M \ D) : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 h1
      push_cast at this ⊢
      exact this
    have hM1' : 1 / (M : ℝ) ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le (by positivity) hMr
    have hMN : (M : ℝ) ^ (-(1 / 21 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 21 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hMr (by norm_num)
    linarith
  have hx_den : PPSmooth ⌊(M : ℝ) ^ (1 / 5 : ℝ)⌋₊ (1 - recipSum (Ioc N M \ D)).den := by
    have h1 : PPSmooth ⌊(N : ℝ) ^ (1 / 12 : ℝ)⌋₊ (1 - recipSum (Ioc N M \ D)).den :=
      hDsmooth.of_dvd (Rat.den_ne_zero _) (den_one_sub_dvd _)
    apply h1.mono
    apply Nat.floor_le_floor
    calc (N : ℝ) ^ (1 / 12 : ℝ) ≤ (M : ℝ) ^ (1 / 12 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hMr (by norm_num)
      _ ≤ (M : ℝ) ^ (1 / 5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  obtain ⟨Y, hYsub, hYsum⟩ := hM₀ M (by omega) _ hx_ge hx_le hx_den
  -- the final interval bound `(1 + η) M ≤ (e + ε) N`
  have h12 : 12 / ε ≤ (N : ℝ) := Nat.ceil_le.1 hNε
  have h6 : 6 ≤ ε / 2 * N := by
    have h := mul_le_mul_of_nonneg_left h12 (by positivity : (0 : ℝ) ≤ ε / 2)
    have e : ε / 2 * (12 / ε) = 6 := by field_simp; ring
    linarith
  have hηN : η * Real.exp 1 * N ≤ ε / 2 * N := mul_le_mul_of_nonneg_right hηe (by positivity)
  have hbound : (1 + η) * (M : ℝ) ≤ (Real.exp 1 + ε) * N := by
    have h1 : (1 + η) * (M : ℝ) ≤ (1 + η) * (Real.exp 1 * N + 3) :=
      mul_le_mul_of_nonneg_left hM2 (by positivity)
    have e : (1 + η) * (Real.exp 1 * N + 3) = Real.exp 1 * N + η * Real.exp 1 * N + 3 + 3 * η := by
      ring
    nlinarith
  have hU : ⌊(1 + η) * (M : ℝ)⌋₊ ≤ ⌊(Real.exp 1 + ε) * N⌋₊ := Nat.floor_le_floor hbound
  have hMU : M ≤ ⌊(Real.exp 1 + ε) * N⌋₊ := by
    apply Nat.le_floor
    have : (M : ℝ) ≤ (1 + η) * M := by nlinarith
    linarith
  refine ⟨(Ioc N M \ D) ∪ Y, ?_, ?_⟩
  · intro m hm
    rcases Finset.mem_union.1 hm with hm | hm
    · have h1 := (Finset.mem_sdiff.1 hm).1
      rw [Finset.mem_Ioc] at h1 ⊢
      exact ⟨h1.1, h1.2.trans hMU⟩
    · have h1 := hYsub hm
      rw [Finset.mem_Ioc] at h1 ⊢
      exact ⟨hNM.trans h1.1, h1.2.trans hU⟩
  · have hdisj : Disjoint (Ioc N M \ D) Y := by
      rw [Finset.disjoint_left]
      intro a ha haY
      have h1 := (Finset.mem_sdiff.1 ha).1
      have h2 := hYsub haY
      rw [Finset.mem_Ioc] at h1 h2
      omega
    rw [recipSum_union hdisj, hYsum]
    ring

/-- The trivial lower bound: if distinct integers in `(N, U]` have reciprocal sum `1`, then
`U ≥ e N`. -/
theorem croot_lower {N U : ℕ} (hN : 1 ≤ N) {X : Finset ℕ} (hX : X ⊆ Ioc N U)
    (h : recipSum X = 1) : Real.exp 1 * N ≤ U := by
  have hNU : N ≤ U := by
    by_contra hlt
    push Not at hlt
    rw [Finset.Ioc_eq_empty_of_le hlt.le, Finset.subset_empty] at hX
    rw [hX, recipSum_empty] at h
    exact zero_ne_one h
  have h1 : (1 : ℝ) ≤ Real.log ((U : ℝ) / N) := by
    have h2 : recipSum X ≤ recipSum (Ioc N U) := recipSum_mono hX
    have h3 := recipSum_Ioc_le_log hN hNU
    have h4 : ((recipSum X : ℚ) : ℝ) ≤ ((recipSum (Ioc N U) : ℚ) : ℝ) := by exact_mod_cast h2
    rw [h] at h4
    push_cast at h4
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hUpos : (0 : ℝ) < U := by exact_mod_cast (lt_of_lt_of_le hN hNU)
  have h5 : Real.exp 1 ≤ (U : ℝ) / N := by
    rw [← Real.exp_log (div_pos hUpos hNpos)]
    exact Real.exp_le_exp.2 h1
  rwa [le_div_iff₀ hNpos] at h5

/-! ## The shortest interval -/

/-- `shortestEnd N` is the least `U` such that some set of distinct integers in `(N, U]` has
reciprocal sum `1` (and `0` if there is no such `U`). -/
noncomputable def shortestEnd (N : ℕ) : ℕ :=
  sInf {U : ℕ | ∃ X ⊆ Finset.Ioc N U, recipSum X = 1}

/-- **Answer to JSP-000243 / Erdős–Graham**: the shortest interval `(N, U]` containing distinct
integers whose reciprocals sum to one has `U ~ e N`, i.e. width `(e - 1 + o(1)) N`. -/
theorem tendsto_shortestEnd :
    Tendsto (fun N : ℕ => (shortestEnd N : ℝ) / N) atTop (nhds (Real.exp 1)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [croot_upper 1 one_pos, Filter.eventually_ge_atTop 1] with N hN hN1
    have hne : {U : ℕ | ∃ X ⊆ Finset.Ioc N U, recipSum X = 1}.Nonempty := ⟨_, hN⟩
    obtain ⟨X, hX, hXs⟩ := Nat.sInf_mem hne
    have hlow := croot_lower hN1 hX hXs
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [lt_div_iff₀ hNpos]
    calc a * N < Real.exp 1 * N := mul_lt_mul_of_pos_right ha hNpos
      _ ≤ shortestEnd N := hlow
  · intro a ha
    have hε0 : 0 < (a - Real.exp 1) / 2 := by linarith
    filter_upwards [croot_upper _ hε0, Filter.eventually_ge_atTop 1] with N hN hN1
    have hle : shortestEnd N ≤ ⌊(Real.exp 1 + (a - Real.exp 1) / 2) * N⌋₊ := Nat.sInf_le hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [div_lt_iff₀ hNpos]
    calc (shortestEnd N : ℝ) ≤ (⌊(Real.exp 1 + (a - Real.exp 1) / 2) * N⌋₊ : ℝ) := by
          exact_mod_cast hle
      _ ≤ (Real.exp 1 + (a - Real.exp 1) / 2) * N := Nat.floor_le (by positivity)
      _ < a * N := by nlinarith

/-! ## The questions of Erdős and Graham -/

/-- A nonempty finite set of integers `≥ 2` whose reciprocals sum to `1`. -/
def Admissible (X : Finset ℕ) : Prop := X.Nonempty ∧ (∀ x ∈ X, 2 ≤ x) ∧ recipSum X = 1

/-- `x_max / x_min ≤ C` for the finite set `X`. -/
def RatioLE (X : Finset ℕ) (C : ℝ) : Prop := ∀ a ∈ X, ∀ b ∈ X, (a : ℝ) ≤ C * b

/-- For every `ε > 0` there are infinitely many admissible sets with `x_max / x_min ≤ e + ε`. -/
theorem infinite_admissible_ratio_le (ε : ℝ) (hε : 0 < ε) :
    {X : Finset ℕ | Admissible X ∧ RatioLE X (Real.exp 1 + ε)}.Infinite := by
  -- the maps `X ↦ max X` is unbounded on this family
  have hunb : ¬ BddAbove ((fun X : Finset ℕ => X.sup id) ''
      {X : Finset ℕ | Admissible X ∧ RatioLE X (Real.exp 1 + ε)}) := by
    rintro ⟨K, hK⟩
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (croot_upper ε hε)
    obtain ⟨X, hX, hXs⟩ := hN₀ (max N₀ (K + 1)) (le_max_left _ _)
    set N := max N₀ (K + 1) with hN
    have hXne : X.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      rw [recipSum_empty] at hXs
      exact zero_ne_one hXs
    have hmem : X ∈ {X : Finset ℕ | Admissible X ∧ RatioLE X (Real.exp 1 + ε)} := by
      refine ⟨⟨hXne, fun x hx => ?_, hXs⟩, fun a ha b hb => ?_⟩
      · have := (Finset.mem_Ioc.1 (hX hx)).1
        omega
      · have ha' := (Finset.mem_Ioc.1 (hX ha)).2
        have hb' := (Finset.mem_Ioc.1 (hX hb)).1
        have h1 : (a : ℝ) ≤ (Real.exp 1 + ε) * N :=
          (Nat.cast_le.2 ha').trans (Nat.floor_le (by positivity))
        have h2 : (N : ℝ) ≤ b := by exact_mod_cast hb'.le
        have h3 : (Real.exp 1 + ε) * N ≤ (Real.exp 1 + ε) * b :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        linarith
    have hle := hK ⟨X, hmem, rfl⟩
    obtain ⟨x, hx⟩ := hXne
    have h1 : x ≤ X.sup id := Finset.le_sup (f := id) hx
    have h2 := (Finset.mem_Ioc.1 (hX hx)).1
    have h3 : K + 1 ≤ N := le_max_right _ _
    simp only at hle
    omega
  intro hfin
  exact hunb (hfin.image _).bddAbove

/-- **Erdős–Graham, question 1**: there are infinitely many sets `2 ≤ x₁ < ⋯ < x_k` with
`∑ 1/xᵢ = 1` and `x_k / x₁` bounded. -/
theorem erdos_graham_q1 : ∃ C : ℝ, {X : Finset ℕ | Admissible X ∧ RatioLE X C}.Infinite :=
  ⟨Real.exp 1 + 1, infinite_admissible_ratio_le 1 one_pos⟩

/-- Only finitely many admissible sets have `x_max / x_min ≤ e - ε` (the "trivial" bound). -/
theorem finite_admissible_ratio_le (ε : ℝ) (hε : 0 < ε) :
    {X : Finset ℕ | Admissible X ∧ RatioLE X (Real.exp 1 - ε)}.Finite := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set L : ℕ := ⌊Real.exp 1 * Real.exp 1 / ε⌋₊ + 1 with hL
  apply ((Finset.range L).powerset.finite_toSet).subset
  rintro X ⟨⟨hXne, hX2, hXs⟩, hratio⟩
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
  -- `m = min X`, `U = max X`
  set m := X.min' hXne with hm
  set U := X.max' hXne with hU
  have hm2 : 2 ≤ m := hX2 m (Finset.min'_mem X hXne)
  have hsub : X ⊆ Ioc (m - 1) U := by
    intro a ha
    rw [Finset.mem_Ioc]
    have h1 : m ≤ a := Finset.min'_le X a ha
    have h2 : a ≤ U := Finset.le_max' X a ha
    omega
  have hlow := croot_lower (by omega) hsub hXs
  have hrat := hratio U (Finset.max'_mem X hXne) m (Finset.min'_mem X hXne)
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hm1] at hlow
  -- `e (m - 1) ≤ U ≤ (e - ε) m`, hence `ε m ≤ e`
  have hmle : ε * m ≤ Real.exp 1 := by nlinarith
  intro a ha
  rw [Finset.mem_range]
  have ha' := hratio a ha m (Finset.min'_mem X hXne)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmε : (m : ℝ) ≤ Real.exp 1 / ε := by rw [le_div_iff₀ hε]; linarith
  have hεm : (Real.exp 1 - ε) * m ≤ Real.exp 1 * (Real.exp 1 / ε) := by
    have := mul_le_mul_of_nonneg_left hmε he.le
    nlinarith
  have h1 : (a : ℝ) ≤ Real.exp 1 * Real.exp 1 / ε := by
    have e : Real.exp 1 * (Real.exp 1 / ε) = Real.exp 1 * Real.exp 1 / ε := by ring
    linarith
  have h2 : a ≤ ⌊Real.exp 1 * Real.exp 1 / ε⌋₊ := Nat.le_floor h1
  omega

/-- The admissible sets `{x₁ < ⋯ < x_k}` (`2 ≤ x₁`, `∑ 1/xᵢ = 1`) as a type. -/
abbrev AdmSet : Type := {X : Finset ℕ // Admissible X}

/-- The ratio `x_k / x₁` of the largest to the smallest element of an admissible set. -/
noncomputable def AdmSet.ratio (X : AdmSet) : ℝ :=
  (X.1.max' X.2.1 : ℝ) / (X.1.min' X.2.1 : ℝ)

lemma AdmSet.ratio_le_iff (X : AdmSet) (C : ℝ) : X.ratio ≤ C ↔ RatioLE X.1 C := by
  have hmin2 : 2 ≤ X.1.min' X.2.1 := X.2.2.1 _ (Finset.min'_mem _ _)
  have hmin_pos : (0 : ℝ) < X.1.min' X.2.1 := by
    have : 0 < X.1.min' X.2.1 := by omega
    exact_mod_cast this
  have hmax_pos : (0 : ℝ) < X.1.max' X.2.1 := by
    have : X.1.min' X.2.1 ≤ X.1.max' X.2.1 := Finset.min'_le_max' _ X.2.1
    have : (X.1.min' X.2.1 : ℝ) ≤ X.1.max' X.2.1 := by exact_mod_cast this
    linarith
  unfold AdmSet.ratio RatioLE
  rw [div_le_iff₀ hmin_pos]
  constructor
  · intro h a ha b hb
    have h1 : (a : ℝ) ≤ X.1.max' X.2.1 := by exact_mod_cast Finset.le_max' _ _ ha
    have h2 : (X.1.min' X.2.1 : ℝ) ≤ b := by exact_mod_cast Finset.min'_le _ _ hb
    have hC : 0 ≤ C := by
      by_contra hC
      push Not at hC
      have : C * (X.1.min' X.2.1 : ℝ) < 0 := mul_neg_of_neg_of_pos hC hmin_pos
      linarith
    have h3 : C * (X.1.min' X.2.1 : ℝ) ≤ C * b := mul_le_mul_of_nonneg_left h2 hC
    linarith
  · intro h
    exact h _ (Finset.max'_mem _ _) _ (Finset.min'_mem _ _)

/-- **Erdős–Graham, question 2**: `liminf x_k / x₁ = e`, the `liminf` being taken over all
admissible sets `{x₁ < ⋯ < x_k}` (along the cofinite filter). -/
theorem liminf_ratio_eq_exp_one :
    Filter.liminf AdmSet.ratio Filter.cofinite = Real.exp 1 := by
  have hpos : ∀ X : AdmSet, 0 ≤ X.ratio := fun X => by unfold AdmSet.ratio; positivity
  have hbdd : Filter.IsBoundedUnder (· ≥ ·) Filter.cofinite AdmSet.ratio :=
    Filter.isBoundedUnder_of ⟨0, hpos⟩
  have hfreq : ∀ ε > 0, ∃ᶠ X in Filter.cofinite, AdmSet.ratio X ≤ Real.exp 1 + ε := by
    intro ε hε
    rw [Filter.frequently_cofinite_iff_infinite]
    apply Set.Infinite.of_image Subtype.val
    apply (infinite_admissible_ratio_le ε hε).mono
    rintro X ⟨hadm, hrat⟩
    exact ⟨⟨X, hadm⟩, (AdmSet.ratio_le_iff _ _).2 hrat, rfl⟩
  have hcobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.cofinite AdmSet.ratio := by
    refine ⟨Real.exp 1 + 1, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨X, hX1, hX2⟩ := ((hfreq 1 one_pos).and_eventually ha).exists
    show a ≤ Real.exp 1 + 1
    linarith
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have h := Filter.liminf_le_of_frequently_le
      (hfreq ((Filter.liminf AdmSet.ratio Filter.cofinite - Real.exp 1) / 2) (by linarith)) hbdd
    linarith
  · by_contra hlt
    push Not at hlt
    set ε := (Real.exp 1 - Filter.liminf AdmSet.ratio Filter.cofinite) / 2 with hε
    have hε0 : 0 < ε := by linarith
    have h : Real.exp 1 - ε ≤ Filter.liminf AdmSet.ratio Filter.cofinite := by
      apply Filter.le_liminf_of_le hcobdd
      rw [Filter.eventually_cofinite]
      apply ((finite_admissible_ratio_le ε hε0).preimage Subtype.val_injective.injOn).subset
      intro X hX
      simp only [Set.mem_ofPred_eq, not_le] at hX
      exact ⟨X.2, (AdmSet.ratio_le_iff X _).1 hX.le⟩
    linarith

end Croot
