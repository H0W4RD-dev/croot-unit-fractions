# Unit fractions with denominators in short intervals — a Lean 4 formalization of Croot's theorem

This repository contains a complete, `sorry`-free Lean 4 / Mathlib formalization of
**Ernest S. Croot III's solution** of the Erdős–Graham problem on the *shortest interval
containing distinct denominators whose reciprocals sum to one*:

* Justin Sun Prize catalog: **JSP-000243**, "What is the shortest integer interval containing
  distinct denominators whose reciprocals sum to one?"
* Erdős Problems: **#286**.
* Original source: P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial
  Number Theory*, Monographies de L'Enseignement Mathématique 28, Genève, 1980, **p. 33**
  (Chapter 4, Egyptian fractions).

## Credit

* **Problem:** Paul Erdős and Ronald L. Graham (1980).
* **Mathematical solution:** Ernest S. Croot III, *On unit fractions with denominators in short
  intervals*, Acta Arithmetica **99** (2001), no. 2, 99–114,
  [doi:10.4064/aa99-2-1](https://doi.org/10.4064/aa99-2-1); preprint
  [arXiv:math/9904181](https://arxiv.org/abs/math/9904181) (April 1999), Main Theorem.
  All mathematical ideas used here (harmonic block, elimination of large prime powers using
  Lemma 1, exact representation via finite Fourier analysis modulo `lcm(1,…,y)` with
  Lemma 4) are Croot's.
* **Lean formalization:** this repository. The formalization follows Croot's argument, with
  the routine adjustments listed under "Differences from the paper" so that only
  Chebyshev-strength prime estimates already in Mathlib are needed.
  It was produced with substantial AI assistance (Claude, Anthropic).

## The questions and the formal answers

Erdős and Graham asked (as quoted in Croot's paper):

1. Are there infinitely many sets of integers `2 ≤ x₁ < x₂ < ⋯ < x_k` (`k` variable) with
   `1 = 1/x₁ + ⋯ + 1/x_k` for which `x_k / x₁` is bounded?
2. If so, what is `liminf x_k / x₁` over all such sets? (Trivially `≥ e`; is it `= e`?)

Equivalently (JSP-000243): what is the shortest interval containing distinct denominators whose
reciprocals sum to one? Croot's Main Theorem answers this: for every large `N` such
denominators exist in `(N, (e + o(1)) N]`, and trivially no interval `(N, U]` with `U < e N` works.

All statements are in `Croot/Main.lean`, namespace `Croot`. Here
`recipSum X = ∑_{n ∈ X} 1/n : ℚ` (`Croot/Basic.lean`).

```lean
/-- Croot's theorem (Main Theorem, r = 1): ∀ ε > 0, for all large N there are distinct
integers in (N, (e + ε) N] whose reciprocals sum to 1. -/
theorem Croot.croot_upper (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,
    ∃ X ⊆ Finset.Ioc N ⌊(Real.exp 1 + ε) * N⌋₊, recipSum X = 1

/-- The matching (trivial) lower bound. -/
theorem Croot.croot_lower {N U : ℕ} (hN : 1 ≤ N) {X : Finset ℕ} (hX : X ⊆ Finset.Ioc N U)
    (h : recipSum X = 1) : Real.exp 1 * N ≤ U

/-- JSP-000243: the shortest interval (N, U] containing distinct denominators whose
reciprocals sum to one has U / N → e (width (e - 1 + o(1)) N). -/
noncomputable def Croot.shortestEnd (N : ℕ) : ℕ :=
  sInf {U : ℕ | ∃ X ⊆ Finset.Ioc N U, recipSum X = 1}
theorem Croot.tendsto_shortestEnd :
    Tendsto (fun N : ℕ => (shortestEnd N : ℝ) / N) atTop (nhds (Real.exp 1))

/-- Erdős–Graham question 1. -/
def Croot.Admissible (X : Finset ℕ) : Prop := X.Nonempty ∧ (∀ x ∈ X, 2 ≤ x) ∧ recipSum X = 1
def Croot.RatioLE (X : Finset ℕ) (C : ℝ) : Prop := ∀ a ∈ X, ∀ b ∈ X, (a : ℝ) ≤ C * b
theorem Croot.erdos_graham_q1 : ∃ C : ℝ, {X : Finset ℕ | Admissible X ∧ RatioLE X C}.Infinite

/-- Erdős–Graham question 2: liminf x_k / x₁ = e over all admissible sets. -/
abbrev Croot.AdmSet : Type := {X : Finset ℕ // Admissible X}
noncomputable def Croot.AdmSet.ratio (X : AdmSet) : ℝ :=
  (X.1.max' X.2.1 : ℝ) / (X.1.min' X.2.1 : ℝ)
theorem Croot.liminf_ratio_eq_exp_one :
    Filter.liminf AdmSet.ratio Filter.cofinite = Real.exp 1
```

The `liminf` statement is also given in elementary form:
`Croot.infinite_admissible_ratio_le` (for every `ε > 0` infinitely many admissible sets have
`x_k ≤ (e + ε) x₁`) and `Croot.finite_admissible_ratio_le` (only finitely many have
`x_k ≤ (e − ε) x₁`).

### Statement correspondence

* A finite set `X : Finset ℕ` is the same thing as distinct integers `x₁ < ⋯ < x_k`; `recipSum`
  is the exact rational sum `∑ 1/xᵢ` (no floating point; division by `0` never occurs since
  all elements are `> N ≥ 0`, resp. `≥ 2`).
* `croot_upper` is the `r = 1` case of Croot's Main Theorem with the error term `o(1)`
  (stated as: for every `ε > 0`, eventually). `Finset.Ioc N ⌊(e+ε)N⌋₊` is exactly the set of
  integers `x` with `N < x ≤ (e + ε) N`.
* Question 1 ("infinitely many sets with `x_k / x₁` bounded") is `erdos_graham_q1`, where
  `RatioLE X C` says `x_k ≤ C x₁` (equivalently `a ≤ C b` for all `a, b ∈ X`).
* Question 2 ("`liminf x_k/x₁ = e` over all such sets") is `liminf_ratio_eq_exp_one`; the
  liminf is taken over the (countably infinite) family of admissible sets with the cofinite
  filter, i.e. as the sets range over all admissible sets, each counted once.
* The JSP phrasing ("shortest interval") is `tendsto_shortestEnd`: the least right end point
  `U` of an interval `(N, U]` containing such a set satisfies `U ∼ e N`.

## Differences from the paper (scope)

* Only the case `r = 1` (the one relevant to the problem) is formalized, and the error term is
  `o(1)` rather than `O(log log N / log N)`; neither the general rational `r` nor the explicit
  error term is needed to answer the problem.
* The prime-number-theorem inputs of the paper are replaced by Chebyshev-type estimates (in
  Mathlib: `Chebyshev.theta_le_log4_mul_x`, `Nat.two_pow_le_mul_lcmUpto`, …):
  prime counts in ranges `(x, 2.7x]` (`Croot/Primes.lean`), positive density of
  prime-power-smooth numbers via products of primes from disjoint ranges
  (`Croot/SmoothDensity.lean`), and the core construction with cofactors `p^b ℓ₁ ℓ₂ k`
  (`Croot/Core.lean`).
* The exponents in Lemma 1 and the parameters of Proposition 2 are chosen with some slack
  (e.g. denominators `⌊N^{1/12}⌋`-pp-smooth after Proposition 1; `y = ⌊M^{1/5}⌋`,
  `X = M^{3/4} (log M)^4` in Proposition 2).

A detailed account of the proof as formalized is in [`PROOF.md`](PROOF.md); build and audit
results for the selected commit are recorded in [`VERIFICATION.md`](VERIFICATION.md).

## File overview

| File | Content |
| --- | --- |
| `Croot/Basic.lean` | `recipSum`, `PPSmooth` (prime-power smoothness), denominators of reciprocal sums |
| `Croot/Harmonic.lean` | `log`-bounds for `∑_{N<n≤M} 1/n`; the harmonic block `(N, M]`, `e N ≤ M ≤ e N + 3` |
| `Croot/Primes.lean` | Chebyshev-type estimates: primes in `(x, 2.7x]`, prime powers, `∑ 1/q → 0` |
| `Croot/Lemma1.lean` | Croot's Lemma 1 (subset sums of inverses of primes cover `ℤ/n`), Fourier on `ZMod n` |
| `Croot/ElimAlgebra.lean` | the denominator algebra of one elimination step |
| `Croot/SmoothExist.lean` | pp-smooth integers in `[Z, 4Z]` coprime to a given prime |
| `Croot/Prop1.lean` | Croot's Proposition 1 (clearing large prime powers from the denominator) |
| `Croot/Fourier.lean` | the counting identity over `P = lcm(1..y)` and the term estimates |
| `Croot/SmoothDensity.lean` | positive density / reciprocal mass of pp-smooth numbers |
| `Croot/Core.lean` | the core elements and the far-point lemma (Croot's Lemma 4) |
| `Croot/Asymptotics.lean` | elementary "for `M` large" inequalities |
| `Croot/Prop2.lean` | Croot's Proposition 2 (exact representation in `(M, (1+η)M]`) |
| `Croot/Main.lean` | assembly: `croot_upper`, `croot_lower`, Erdős–Graham answers |

## Building and checking

Lean `v4.33.1` (see `lean-toolchain`) and Mathlib `v4.33.1` (pinned in `lake-manifest.json`).

```bash
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
lake env lean scripts/Statements.lean
```

`scripts/Axioms.lean` prints the axioms of every main theorem; each depends only on
`propext`, `Classical.choice` and `Quot.sound`:

```
'Croot.croot_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.croot_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.tendsto_shortestEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.erdos_graham_q1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.infinite_admissible_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.finite_admissible_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.liminf_ratio_eq_exp_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`scripts/Statements.lean` restates the main results using only Mathlib notions (no
definitions from this repository — e.g. the sum `∑ x ∈ X, (1 : ℚ) / x` instead of
`recipSum`) and derives them from the theorems above, so that the statements can be checked
without reading the project's definitions.

The project contains no `sorry`, `admit`, `axiom` declarations or `native_decide`.

## License

Apache-2.0 (see `LICENSE`).
