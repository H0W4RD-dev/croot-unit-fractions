import Croot.Main
import Croot.Erdos286

/-!
# Self-contained restatements of the main results

Each statement below is written with Mathlib notions only (no definitions from this
repository) and is derived from the main theorems of `Croot/Main.lean`.  This makes the
statement correspondence checkable without reading `Croot.recipSum`, `Croot.Admissible`, etc.

Run with `lake env lean scripts/Statements.lean`.
-/

open Filter

/-- **Croot's theorem** (Main Theorem of Croot 2001, case `r = 1`, error `o(1)`): for every
`ε > 0` and all sufficiently large `N` there are distinct integers `N < x₁ < ⋯ < x_k ≤ (e + ε) N`
with `1/x₁ + ⋯ + 1/x_k = 1`. -/
theorem croot_upper_plain (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∃ X : Finset ℕ,
    (∀ x ∈ X, N < x ∧ (x : ℝ) ≤ (Real.exp 1 + ε) * N) ∧ ∑ x ∈ X, (1 : ℚ) / x = 1 := by
  filter_upwards [Croot.croot_upper ε hε] with N hN
  obtain ⟨X, hX, hXs⟩ := hN
  refine ⟨X, fun x hx => ?_, hXs⟩
  have h := Finset.mem_Ioc.1 (hX hx)
  exact ⟨h.1, (Nat.cast_le.2 h.2).trans (Nat.floor_le (by positivity))⟩

/-- The trivial converse: distinct integers in `(N, U]` with reciprocal sum `1` force
`U ≥ e N`. -/
theorem croot_lower_plain (N U : ℕ) (hN : 1 ≤ N) (X : Finset ℕ) (hX : ∀ x ∈ X, N < x ∧ x ≤ U)
    (hs : ∑ x ∈ X, (1 : ℚ) / x = 1) : Real.exp 1 * N ≤ U :=
  Croot.croot_lower hN (fun x hx => Finset.mem_Ioc.2 (hX x hx)) hs

/-- **JSP-000243** ("What is the shortest integer interval containing distinct denominators
whose reciprocals sum to one?"): the least `U` such that `(N, U]` contains distinct
denominators with reciprocal sum one satisfies `U / N → e`. -/
theorem shortest_interval_plain :
    Tendsto (fun N : ℕ => ((sInf {U : ℕ | ∃ X : Finset ℕ, (∀ x ∈ X, N < x ∧ x ≤ U) ∧
      ∑ x ∈ X, (1 : ℚ) / x = 1} : ℕ) : ℝ) / N) atTop (nhds (Real.exp 1)) := by
  have h : ∀ N : ℕ, {U : ℕ | ∃ X : Finset ℕ, (∀ x ∈ X, N < x ∧ x ≤ U) ∧
      ∑ x ∈ X, (1 : ℚ) / x = 1} = {U : ℕ | ∃ X ⊆ Finset.Ioc N U, Croot.recipSum X = 1} := by
    intro N
    ext U
    constructor
    · rintro ⟨X, hX, hs⟩
      exact ⟨X, fun x hx => Finset.mem_Ioc.2 (hX x hx), hs⟩
    · rintro ⟨X, hX, hs⟩
      exact ⟨X, fun x hx => Finset.mem_Ioc.1 (hX hx), hs⟩
  simp only [h]
  exact Croot.tendsto_shortestEnd

/-- **Erdős–Graham, question 1**: there are infinitely many finite sets of integers
`2 ≤ x₁ < ⋯ < x_k` with `∑ 1/xᵢ = 1` and `x_k / x₁` bounded. -/
theorem erdos_graham_q1_plain : ∃ C : ℝ, {X : Finset ℕ | X.Nonempty ∧ (∀ x ∈ X, 2 ≤ x) ∧
    ∑ x ∈ X, (1 : ℚ) / x = 1 ∧ ∀ a ∈ X, ∀ b ∈ X, (a : ℝ) ≤ C * b}.Infinite := by
  obtain ⟨C, hC⟩ := Croot.erdos_graham_q1
  refine ⟨C, hC.mono ?_⟩
  rintro X ⟨⟨h1, h2, h3⟩, h4⟩
  exact ⟨h1, h2, h3, h4⟩

/-- **Erdős–Graham, question 2**: `liminf x_k / x₁ = e`, the `liminf` being taken over all
finite sets `2 ≤ x₁ < ⋯ < x_k` with `∑ 1/xᵢ = 1` (along the cofinite filter, i.e. as the set
ranges over all such sets, each counted once). -/
theorem erdos_graham_q2_plain : Filter.liminf
    (fun X : {X : Finset ℕ // X.Nonempty ∧ (∀ x ∈ X, 2 ≤ x) ∧ ∑ x ∈ X, (1 : ℚ) / x = 1} =>
      ((X.1.max' X.2.1 : ℕ) : ℝ) / ((X.1.min' X.2.1 : ℕ) : ℝ)) Filter.cofinite =
    Real.exp 1 :=
  Croot.liminf_ratio_eq_exp_one

/-- **Erdős Problem #286, erdosproblems.com / formal-conjectures phrasing**: the statement
`Erdos286.erdos_286` of google-deepmind/formal-conjectures, verbatim except that `answer(True)`
is replaced by its value `True`. -/
theorem erdos_286_formal_conjectures : True ↔ ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧
    ∀ᶠ k : ℕ in atTop, ∃ a b : ℝ, b - a = (Real.exp 1 - 1 + o k) * k ∧
      ∃ S : Finset ℕ, S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℝ) / n = 1 ∧
        ∀ n ∈ S, (n : ℝ) ∈ Set.Icc a b :=
  Croot.erdos_286_iff

/-- `k` distinct positive integers in `[a, b]`, listed increasingly, with reciprocal sum `1`
(the encoding used by the comparator challenge `ComparatorChallenges/ErdosProblems/Erdos286.lean`
of plby/lean-proofs). -/
def IntervalRep (k : ℕ) (a b : ℝ) : Prop :=
  ∃ n : Fin k → ℕ, StrictMono n ∧ 0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i ∧
    ∀ i, (n i : ℝ) ∈ Set.Icc a b

/-- Erdős Problem #286 in the comparator-challenge encoding (little-o error term, `2 ≤ k`). -/
theorem erdos_286_comparator_form : ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ k : ℕ in atTop, 2 ≤ k ∧ ∃ a b : ℝ, b - a = (Real.exp 1 - 1 + o k) * k ∧
      IntervalRep k a b := by
  refine ⟨fun _ => 0, Asymptotics.isLittleO_zero _ _, ?_⟩
  filter_upwards [Croot.erdos_286_zero, Filter.eventually_ge_atTop 2] with k hk hk2
  obtain ⟨a, b, hab, S, hS, h0, hsum, hmem⟩ := hk
  refine ⟨hk2, a, b, by rw [hab]; ring, S.orderEmbOfFin hS, (S.orderEmbOfFin hS).strictMono,
    ?_, ?_, fun i => hmem _ (Finset.orderEmbOfFin_mem S hS i)⟩
  · rw [Finset.range_orderEmbOfFin]
    exact_mod_cast h0
  · have e : ∑ i, (1 : ℝ) / ((S.orderEmbOfFin hS) i : ℕ) = ∑ n ∈ S, (1 : ℝ) / n := by
      conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S hS]
      rw [Finset.sum_map]
      rfl
    rw [e, hsum]

#print axioms croot_upper_plain
#print axioms croot_lower_plain
#print axioms shortest_interval_plain
#print axioms erdos_graham_q1_plain
#print axioms erdos_graham_q2_plain
#print axioms erdos_286_formal_conjectures
#print axioms erdos_286_comparator_form
