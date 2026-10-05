import Croot.Main

/-!
# The erdosproblems.com / formal-conjectures statement of Erdős Problem #286

The website erdosproblems.com phrases Problem #286 as: *for `k ≥ 2`, is there an interval `I` of
width `(e - 1 + o(1)) k` and integers `n₁ < ⋯ < n_k ∈ I` with `1 = ∑ 1/nᵢ`?*  This is the
statement formalized in `google-deepmind/formal-conjectures` (`Erdos286.erdos_286`).  We derive
it from Croot's theorem (`Croot.croot_upper`), with `o ≡ 0`.

Croot's theorem with `ε = 1/1000` gives `X ⊆ (N, U]`, `U = ⌊(e + ε) N⌋`, with `∑_{x∈X} 1/x = 1`.
Since `∑_{N<n≤U} 1/n ≤ log (U/N) ≤ 1 + ε/e`, the complement `C = (N, U] \ X` is tiny
(`#C ≤ 3N/2000`), so `#X` is within `#C + 2` of any `k ∈ [c N, c (N+1))`, `c = e - 1 + ε`.
The missing terms are created with `1/(12t) = 1/(21t) + 1/(28t)` for `t ∈ [0.13N, 0.139N]`
(such `12t` lie in `X` except for at most `#C` values; `21t, 28t > U` are new and distinct), so
the final set has exactly `k` elements, all in `(N, 3.892 N] ⊆ [N, N + (e - 1) k]`.
-/

namespace Croot

open Real Finset Filter

/-- A set of integers in `(0, U]` has reciprocal sum at least `#S / U`. -/
lemma card_div_le_recipSum {S : Finset ℕ} {U : ℕ} (hU : 0 < U) (h : ∀ m ∈ S, 0 < m ∧ m ≤ U) :
    (S.card : ℝ) / U ≤ ((recipSum S : ℚ) : ℝ) := by
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  rw [recipSum, Rat.cast_sum]
  calc (S.card : ℝ) / U = ∑ _n ∈ S, (1 : ℝ) / U := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ n ∈ S, (((1 : ℚ) / n : ℚ) : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have h0 : (0 : ℝ) < n := by exact_mod_cast (h n hn).1
        have h1 : (n : ℝ) ≤ U := by exact_mod_cast (h n hn).2
        push_cast
        exact one_div_le_one_div_of_le h0 h1

/-- `recipSum` of an injective image. -/
lemma recipSum_image {T : Finset ℕ} {f : ℕ → ℕ} (hf : Function.Injective f) :
    recipSum (T.image f) = ∑ t ∈ T, (1 : ℚ) / (f t : ℕ) := by
  rw [recipSum, Finset.sum_image (fun a _ b _ h => hf h)]

/-- The count adjustment: a representation from `croot_upper` with `ε = 1/1000` can be turned
into one with exactly `k` terms, for every `k ∈ [c N, c (N+1))`, `c = e - 1 + 1/1000`. -/
lemma exists_card_eq_of_croot {N k : ℕ} {X : Finset ℕ}
    (hX : X ⊆ Ioc N ⌊(Real.exp 1 + 1 / 1000) * N⌋₊) (hXs : recipSum X = 1)
    (hN : 1000 ≤ N)
    (hk1 : (Real.exp 1 - 1 + 1 / 1000) * N ≤ k)
    (hk2 : (k : ℝ) < (Real.exp 1 - 1 + 1 / 1000) * (N + 1)) :
    ∃ S : Finset ℕ, S.card = k ∧ recipSum S = 1 ∧ ∀ n ∈ S, N < n ∧ 1000 * n ≤ 3892 * N := by
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he2 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  set U := ⌊(Real.exp 1 + 1 / 1000) * N⌋₊ with hUdef
  have hNr : (1000 : ℝ) ≤ N := by exact_mod_cast hN
  have hU1 : (U : ℝ) ≤ (Real.exp 1 + 1 / 1000) * N := Nat.floor_le (by positivity)
  have hU2 : (Real.exp 1 + 1 / 1000) * N - 1 < U := Nat.sub_one_lt_floor _
  have hU272 : 100 * U ≤ 272 * N := by
    have : ((100 * U : ℕ) : ℝ) ≤ ((272 * N : ℕ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast this
  have hUlo : 2718 * N ≤ 1000 * U + 1000 := by
    have : ((2718 * N : ℕ) : ℝ) ≤ ((1000 * U + 1000 : ℕ) : ℝ) := by push_cast; nlinarith
    exact_mod_cast this
  have hNU : N ≤ U := by omega
  have hU0 : 0 < U := by omega
  -- the complement `C = (N, U] \ X` has tiny reciprocal mass, hence few elements
  set C := Ioc N U \ X with hCdef
  have hCX : C.card + X.card = U - N := by
    rw [hCdef, Finset.card_sdiff_add_card_eq_card hX, Nat.card_Ioc]
  have hHC : ((recipSum C : ℚ) : ℝ) ≤ 1 / 2000 := by
    have h1 : recipSum C = recipSum (Ioc N U) - 1 := by rw [hCdef, recipSum_sdiff hX, hXs]
    have h2 := recipSum_Ioc_le_log (by omega : 1 ≤ N) hNU
    have hNpos : (0 : ℝ) < N := by positivity
    have hUpos : (0 : ℝ) < U := by exact_mod_cast hU0
    have hpos : (0 : ℝ) < U / N := div_pos hUpos hNpos
    have h3 : Real.log ((U : ℝ) / N) ≤ 1 + 1 / 2000 := by
      have h4 : Real.log ((U : ℝ) / N) - 1 = Real.log ((U : ℝ) / N / Real.exp 1) := by
        rw [Real.log_div hpos.ne' (Real.exp_pos 1).ne', Real.log_exp]
      have h5 := Real.log_le_sub_one_of_pos
        (show 0 < (U : ℝ) / N / Real.exp 1 from div_pos hpos (Real.exp_pos 1))
      have h6 : (U : ℝ) / N / Real.exp 1 ≤ 1 + 1 / 2000 := by
        rw [div_div, div_le_iff₀ (mul_pos hNpos (Real.exp_pos 1))]
        nlinarith
      linarith
    have h7 : ((recipSum C : ℚ) : ℝ) = ((recipSum (Ioc N U) : ℚ) : ℝ) - 1 := by
      rw [h1]; push_cast; ring
    linarith
  have hCcard : 2000 * C.card ≤ 3 * N := by
    have h1 := card_div_le_recipSum hU0 (S := C) (fun m hm => by
      rw [hCdef, Finset.mem_sdiff, Finset.mem_Ioc] at hm
      exact ⟨by omega, hm.1.2⟩)
    have hUpos : (0 : ℝ) < U := by exact_mod_cast hU0
    have h2 : (C.card : ℝ) ≤ U / 2000 := by
      have := h1.trans hHC
      rw [div_le_iff₀ hUpos] at this
      linarith
    have h3 : 2000 * C.card ≤ U := by
      have : ((2000 * C.card : ℕ) : ℝ) ≤ (U : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  -- `#X ≤ k ≤ #X + #C + 2`
  have hXk : X.card ≤ k := by
    have h1 : (X.card : ℝ) + C.card = (U : ℝ) - N := by
      have h' : ((U - N : ℕ) : ℝ) = (U : ℝ) - N := by rw [Nat.cast_sub hNU]
      rw [← h']
      exact_mod_cast (by omega : X.card + C.card = U - N)
    have h2 : (0 : ℝ) ≤ C.card := by positivity
    have : (X.card : ℝ) ≤ k := by nlinarith
    exact_mod_cast this
  have hm : k - X.card ≤ C.card + 2 := by
    have h1 : (X.card : ℝ) + C.card = (U : ℝ) - N := by
      have h' : ((U - N : ℕ) : ℝ) = (U : ℝ) - N := by rw [Nat.cast_sub hNU]
      rw [← h']
      exact_mod_cast (by omega : X.card + C.card = U - N)
    have h2 : (k : ℝ) < X.card + C.card + 3 := by nlinarith
    have h3 : k < X.card + C.card + 3 := by exact_mod_cast h2
    omega
  -- the parameters `t` with `12 t ∈ [1.56 N, 1.668 N]`
  set lo := (13 * N + 99) / 100 with hlo
  set hi := 139 * N / 1000 with hhi
  have hTmem : ∀ t ∈ Finset.Icc lo hi, 13 * N ≤ 100 * t ∧ 1000 * t ≤ 139 * N := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    omega
  have hTcard : (9 * N - 1989) / 1000 + 1 ≤ (Finset.Icc lo hi).card := by
    rw [Nat.card_Icc]
    omega
  set Tset := (Finset.Icc lo hi).filter (fun t => 12 * t ∈ X) with hTsetdef
  have hTset : (Finset.Icc lo hi).card ≤ Tset.card + C.card := by
    have h1 : Tset.card + ((Finset.Icc lo hi).filter (fun t => ¬ 12 * t ∈ X)).card =
        (Finset.Icc lo hi).card :=
      Finset.card_filter_add_card_filter_not (s := Finset.Icc lo hi) (fun t => 12 * t ∈ X)
    have h2 : ((Finset.Icc lo hi).filter (fun t => ¬ 12 * t ∈ X)).card ≤ C.card := by
      have hsub : ((Finset.Icc lo hi).filter (fun t => ¬ 12 * t ∈ X)).image (fun t => 12 * t)
          ⊆ C := by
        intro c hc
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc
        rw [Finset.mem_filter] at ht
        obtain ⟨h1, h2⟩ := hTmem t ht.1
        rw [hCdef, Finset.mem_sdiff, Finset.mem_Ioc]
        exact ⟨⟨by omega, by omega⟩, ht.2⟩
      calc ((Finset.Icc lo hi).filter (fun t => ¬ 12 * t ∈ X)).card
          = (((Finset.Icc lo hi).filter (fun t => ¬ 12 * t ∈ X)).image (fun t => 12 * t)).card :=
            (Finset.card_image_of_injective _ (fun a b h => by
              have h' : 12 * a = 12 * b := h
              omega)).symm
        _ ≤ C.card := Finset.card_le_card hsub
    omega
  have hmT : k - X.card ≤ Tset.card := by omega
  obtain ⟨T', hT'sub, hT'card⟩ := Finset.exists_subset_card_eq hmT
  have hT' : ∀ t ∈ T', (13 * N ≤ 100 * t ∧ 1000 * t ≤ 139 * N) ∧ 12 * t ∈ X := by
    intro t ht
    have := hT'sub ht
    rw [hTsetdef, Finset.mem_filter] at this
    exact ⟨hTmem t this.1, this.2⟩
  have inj12 : Function.Injective (fun t : ℕ => 12 * t) := fun a b h => by
    have h' : 12 * a = 12 * b := h
    omega
  have inj21 : Function.Injective (fun t : ℕ => 21 * t) := fun a b h => by
    have h' : 21 * a = 21 * b := h
    omega
  have inj28 : Function.Injective (fun t : ℕ => 28 * t) := fun a b h => by
    have h' : 28 * a = 28 * b := h
    omega
  set A := T'.image (fun t => 12 * t) with hAdef
  set B₁ := T'.image (fun t => 21 * t) with hB₁def
  set B₂ := T'.image (fun t => 28 * t) with hB₂def
  have hAX : A ⊆ X := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ha
    exact (hT' t ht).2
  have hXmem : ∀ x ∈ X, N < x ∧ x ≤ U := fun x hx => Finset.mem_Ioc.1 (hX hx)
  have hB₁B₂ : Disjoint B₁ B₂ := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨t', ht', he⟩ := Finset.mem_image.1 hb'
    obtain ⟨⟨h1, h2⟩, -⟩ := hT' t ht
    obtain ⟨⟨h1', h2'⟩, -⟩ := hT' t' ht'
    have he' : 28 * t' = 21 * t := he
    omega
  have hXB : Disjoint (X \ A) (B₁ ∪ B₂) := by
    rw [Finset.disjoint_left]
    intro x hx hxB
    have hxU := (hXmem x (Finset.mem_sdiff.1 hx).1).2
    rcases Finset.mem_union.1 hxB with hb | hb
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨⟨h1, h2⟩, -⟩ := hT' t ht
      omega
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨⟨h1, h2⟩, -⟩ := hT' t ht
      omega
  have hAcard : A.card = T'.card := Finset.card_image_of_injective _ inj12
  have hB₁card : B₁.card = T'.card := Finset.card_image_of_injective _ inj21
  have hB₂card : B₂.card = T'.card := Finset.card_image_of_injective _ inj28
  refine ⟨(X \ A) ∪ (B₁ ∪ B₂), ?_, ?_, ?_⟩
  · -- exactly `k` elements
    rw [Finset.card_union_of_disjoint hXB, Finset.card_union_of_disjoint hB₁B₂,
      Finset.card_sdiff_of_subset hAX, hAcard, hB₁card, hB₂card, hT'card]
    have : A.card ≤ X.card := Finset.card_le_card hAX
    omega
  · -- reciprocal sum `1`
    rw [recipSum_union hXB, recipSum_union hB₁B₂, recipSum_sdiff hAX, hXs]
    have key : recipSum B₁ + recipSum B₂ = recipSum A := by
      rw [hB₁def, hB₂def, hAdef, recipSum_image inj21, recipSum_image inj28, recipSum_image inj12,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      obtain ⟨⟨h1, -⟩, -⟩ := hT' t ht
      have ht0 : (t : ℚ) ≠ 0 := by
        have : 0 < t := by omega
        exact_mod_cast this.ne'
      push_cast
      field_simp
      ring
    linarith
  · -- all elements lie in `(N, 3.892 N]`
    intro n hn
    rcases Finset.mem_union.1 hn with hn | hn
    · have := hXmem n (Finset.mem_sdiff.1 hn).1
      omega
    · rcases Finset.mem_union.1 hn with hb | hb
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hb
        obtain ⟨⟨h1, h2⟩, -⟩ := hT' t ht
        omega
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hb
        obtain ⟨⟨h1, h2⟩, -⟩ := hT' t ht
        omega

/-- The cast of `recipSum` to `ℝ` is the real sum of reciprocals. -/
lemma recipSum_cast_real (S : Finset ℕ) :
    ((recipSum S : ℚ) : ℝ) = ∑ n ∈ S, (1 : ℝ) / n := by
  rw [recipSum, Rat.cast_sum]
  push_cast
  rfl

/-- For all large `k` there is an interval of width exactly `(e - 1) k` containing `k` distinct
positive integers whose reciprocals sum to `1`. -/
theorem erdos_286_zero : ∀ᶠ k : ℕ in atTop, ∃ a b : ℝ, b - a = (Real.exp 1 - 1) * k ∧
    ∃ S : Finset ℕ, S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℝ) / n = 1 ∧
      ∀ n ∈ S, (n : ℝ) ∈ Set.Icc a b := by
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he2 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (croot_upper (1 / 1000) (by norm_num))
  set c : ℝ := Real.exp 1 - 1 + 1 / 1000 with hcdef
  have hc : 0 < c := by linarith
  filter_upwards [Filter.eventually_ge_atTop ⌈((max N₀ 1000 : ℕ) + 1 : ℝ) * c⌉₊] with k hk
  set N := ⌊(k : ℝ) / c⌋₊ with hNdef
  have hkc : ((max N₀ 1000 : ℕ) + 1 : ℝ) * c ≤ k := (Nat.ceil_le).1 hk
  have hN : max N₀ 1000 ≤ N := by
    apply Nat.le_floor
    rw [le_div_iff₀ hc]
    nlinarith
  have hN1 : (N : ℝ) ≤ k / c := Nat.floor_le (by positivity)
  have hN2 : (k : ℝ) / c < N + 1 := Nat.lt_floor_add_one _
  have hk1 : c * N ≤ k := by
    rw [le_div_iff₀ hc] at hN1
    linarith
  have hk2 : (k : ℝ) < c * (N + 1) := by
    rw [div_lt_iff₀ hc] at hN2
    linarith
  obtain ⟨X, hX, hXs⟩ := hN₀ N (le_of_max_le_left hN)
  obtain ⟨S, hScard, hSsum, hSmem⟩ :=
    exists_card_eq_of_croot hX hXs (le_of_max_le_right hN) hk1 hk2
  refine ⟨N, N + (Real.exp 1 - 1) * k, by ring, S, hScard, ?_, ?_, ?_⟩
  · intro h0
    have := (hSmem 0 h0).1
    omega
  · rw [← recipSum_cast_real, hSsum, Rat.cast_one]
  · intro n hn
    obtain ⟨h1, h2⟩ := hSmem n hn
    have h1' : (N : ℝ) < n := by exact_mod_cast h1
    have h2' : (1000 : ℝ) * n ≤ 3892 * N := by exact_mod_cast h2
    have hNnn : (0 : ℝ) ≤ N := by positivity
    have hck : (Real.exp 1 - 1) * (c * N) ≤ (Real.exp 1 - 1) * k :=
      mul_le_mul_of_nonneg_left hk1 (by linarith)
    have hec : (2.9 : ℝ) ≤ (Real.exp 1 - 1) * c := by nlinarith
    constructor
    · linarith
    · nlinarith

/-- **Erdős Problem #286 in the erdosproblems.com phrasing** (the statement of
`Erdos286.erdos_286` in google-deepmind/formal-conjectures, with `answer(True)`): for all large
`k` there is an interval of width `(e - 1 + o(1)) k` containing `k` distinct positive integers
whose reciprocals sum to `1`.  Here even `o ≡ 0` works (`erdos_286_zero`). -/
theorem erdos_286 : ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧
    ∀ᶠ k : ℕ in atTop, ∃ a b : ℝ, b - a = (Real.exp 1 - 1 + o k) * k ∧
      ∃ S : Finset ℕ, S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℝ) / n = 1 ∧
        ∀ n ∈ S, (n : ℝ) ∈ Set.Icc a b := by
  refine ⟨fun _ => 0, tendsto_const_nhds, ?_⟩
  filter_upwards [erdos_286_zero] with k hk
  obtain ⟨a, b, hab, hS⟩ := hk
  exact ⟨a, b, by rw [hab]; ring, hS⟩

/-- The same statement in the literal form `answer(True) ↔ …` used by formal-conjectures. -/
theorem erdos_286_iff : True ↔ ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧
    ∀ᶠ k : ℕ in atTop, ∃ a b : ℝ, b - a = (Real.exp 1 - 1 + o k) * k ∧
      ∃ S : Finset ℕ, S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℝ) / n = 1 ∧
        ∀ n ∈ S, (n : ℝ) ∈ Set.Icc a b :=
  ⟨fun _ => erdos_286, fun _ => trivial⟩

end Croot
