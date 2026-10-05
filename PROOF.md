# The proof as formalized

This note describes the mathematical argument checked by the Lean files of this repository.
It is **Croot's proof** (E. S. Croot III, *On unit fractions with denominators in short
intervals*, Acta Arith. 99 (2001), 99–114), specialised to `r = 1` with an `o(1)` error term,
and arranged so that only Chebyshev-strength prime estimates are needed.

Notation: `H(S) = ∑_{n ∈ S} 1/n ∈ ℚ` (`Croot.recipSum`). A positive integer `n` is
*`y`-pp-smooth* (`Croot.PPSmooth y n`) if every prime power exactly dividing `n` is `≤ y`;
equivalently `n ∣ lcm(1, …, y)`. The reduced denominator of `H(S)` divides `lcm S`
(`den_recipSum_dvd`), so it is `y`-pp-smooth when all elements of `S` are.

## 0. Harmonic block (`Croot/Harmonic.lean`)

`log((M+1)/(N+1)) ≤ H((N, M]) ≤ log(M/N)`. With `M` the least integer `> N` with
`H((N, M]) ≥ 1` we get `1 ≤ H((N, M]) < 1 + 1/M` and `e N ≤ M ≤ e N + 3`
(`exists_harmonic_block`).

## 1. Proposition 1: clearing large prime powers (`Croot/Prop1.lean`)

**Statement (`prop1`).** For every `ε > 0` and all large `N`, for `M` as above there is
`D ⊆ (N, M]` with `H(D) ≤ ε`, `H(D) ≥ 1/(20 log N)`, and the reduced denominator of
`H((N, M] \ D)` is `⌊N^{1/12}⌋`-pp-smooth.

*Proof.* Let `Q = ⌊N/(log N)^4⌋`, `y₁ = ⌊N^{1/12}⌋`.

* `D₀` = the elements of `(N, M]` that are not `Q`-pp-smooth. It contains all primes of
  `(N, 2.7N]`, so `H(D₀) ≥ 1/(15 log N)` (Chebyshev lower bound for primes in `(x, 2.7x]`,
  `Croot/Primes.lean`). Each element of `D₀` is a multiple of a prime power `q ∈ (Q, 3N]`, so
  `H(D₀) ≤ ∑_{Q < q ≤ 3N} (1/q)(1 + o(1)) → 0` (Chebyshev upper bounds).
* Downward induction on a threshold `t` from `Q` to `y₁`, keeping the invariant that the
  reduced denominator of `H((N, M] \ D)` is `t`-pp-smooth and that the mass added to `D` so
  far is at most `#{prime powers ≤ Q, > t} · 3(log N)^4/N`. If the denominator is not
  `(t−1)`-pp-smooth then `t = p^a` exactly divides it. Choose a `y₁`-pp-smooth `s ≈ N/(t (log t)^4)`
  with `p ∤ s` (`Croot/SmoothExist.lean`: powers of 2 or 3 times distinct primes from
  `(y/3, y]`), and a set `R` of at least `(log t)^{3.9}` primes `r ∈ (N/(ts), 2.7N/(ts)]`
  not dividing `ps`. By **Lemma 1** there is `T ⊆ R` with
  `∑_{r∈T} r⁻¹ ≡ (num · den'⁻¹ · s) (mod p^a)`; removing `{t s r : r ∈ T}` from the set then
  removes the factor `p^a` from the denominator without creating new prime powers `≥ t`
  (`Croot/ElimAlgebra.lean`, `den_sub_sum_dvd`). The removed mass is `≤ 3 (log N)^4 / N`.
* In total `H(D) ≤ H(D₀) + π*(Q) · 3 (log N)^4 / N → 0`, where `π*(Q) ≪ Q / log Q`.

**Lemma 1 (`Croot/Lemma1.lean`, Croot's Lemma 1).** For all large `n`, if `R` is a set of
primes in `[(log n)^4/4, 3(log n)^4]`, none dividing `n`, with `#R ≥ (log n)^{3.9}`, then
every residue class mod `n` is a subset sum of `{r⁻¹ mod n : r ∈ R}`.
*Proof.* The number of `T ⊆ R` with `∑_{r∈T} r⁻¹ ≡ c` is
`(1/n) ∑_{h mod n} e(−hc/n) ∏_{r∈R} (1 + e(h r⁻¹/n))`. For `h ≢ 0` write `r⁻¹ h ≡ t_r` with
`|t_r| ≤ n/2`. If `|t_r| ≤ n/L` (with `L = (log n)^{2.8}`) for many `r`, then `r t_r − h` is a
multiple of `n` of bounded size for those `r`, and too many primes `≥ (log n)^4/4` would divide
a nonzero integer `≤ n²`; so at least half of the `r` have `|t_r|/n ≥ 1/L`, and for these
`|1 + e(t_r/n)| ≤ 2(1 − 4/L²)`. The product is then `< 2^{#R}/n`, so the `h = 0` term
`2^{#R}/n` dominates and the count is positive.

## 2. Proposition 2: exact representation (`Croot/Prop2.lean`)

**Statement (`prop2`).** For fixed `η ∈ (0, 1]` there is `c > 0` such that for all large `M`,
every rational `x ∈ [M^{−1/21}, c]` whose reduced denominator is `y`-pp-smooth,
`y = ⌊M^{1/5}⌋`, is `H(Y)` for some `Y ⊆ (M, (1 + η) M]`.

*Proof.* Let `P = lcm(1, …, y)`, `B = ⌈16/η⌉`, `W = M^{3/4}`, `X = W (log M)^4`.

* **Rough smooth numbers** (`Croot/SmoothDensity.lean`): the set `G` of `y`-pp-smooth integers
  in `(X, 2X]` with no prime factor `≤ B` has `#G ≥ c_G X`. Construction: products of four
  primes from fixed disjoint ranges `(y^{α_i}, y^{α_{i+1}}]` times a `B`-rough cofactor below
  the smallest range (the factorization is unique, so these products are distinct), and
  Chebyshev gives `∑_{p ∈ range} 1/p ≫ 1`.
  Similarly the `y`-pp-smooth integers in `(M, (1+η)M]` have reciprocal mass `≥ κ η`.
* **Cores** (`Croot/Core.lean`): for `n ∈ G` and each prime `p ≤ y` there is a `y`-pp-smooth
  `m(n, p) ∈ (M, (1+η)M]` divisible by `n` and by `p^{⌊log_p y⌋}`, with
  `m(n,p)/n = p^b ℓ₁ ℓ₂ k` (`ℓ₁, ℓ₂` primes from Chebyshev ranges, `k ≤ B`). Hence
  `lcm_p m(n,p) = P`, and a given `m` arises from at most `(log₂ 2M + 2)^3 B` values of `n`
  (`card_fiber_le`). Let `CA = {m(n,p)}`; `H(CA) ≤ #G (y+1)/M ≤ x/2`.
* **Fill** (`greedy_fill`): add further `y`-pp-smooth integers of `(M,(1+η)M]` one at a time to
  get `Ỹ ⊇ CA` with `2x ≤ H(Ỹ) < 2x + 1/(M+1)` (possible since `2x ≤ 2c ≤ κη`).
* **Counting identity** (`Croot/Fourier.lean`, `fourier_count`): since every `m ∈ Ỹ` divides
  `P` and `xP ∈ ℤ`,
  `∑_{h ∈ window of length P} e(−hx) ∏_{m∈Ỹ}(1 + e(h/m)) = P · #{Z ⊆ Ỹ : H(Z) − x ∈ ℤ}`.
* **Small `|h| ≤ W`**: `e(−hx)∏(1 + e(h/m)) = e(h(H(Ỹ)/2 − x)) ∏ 2cos(πh/m)` has nonnegative
  real part, because `|h/m| < 1/2` and `|h (H(Ỹ)/2 − x)| ≤ 1/4`; the `h = 0` term is
  `2^{#Ỹ}` (`re_term_nonneg`, `term_zero`).
* **Large `W < |h| ≤ P/2`** (Croot's Lemma 4, `exists_far`): for each `n ∈ G`, all elements of
  the core `{m(n,p)}` are multiples of `n > 2W` and their lcm is `P > |h| + W`, so some core
  element `m` has no multiple within distance `W` of `h`. Then `‖h/m‖ ≥ W/((1+η)M) =: δ`
  and `|1 + e(h/m)| ≤ 2(1 − 4δ²)`. These `m` are at least `#G / ((log₂ 2M + 2)^3 B)`
  distinct elements of `Ỹ`, so the term has norm
  `≤ 2^{#Ỹ} exp(−4δ² c_G X /((log₂ 2M+2)^3 B)) ≤ 2^{#Ỹ}/(2P)` (`norm_term_le`,
  `Croot/Asymptotics.lean`).
* Summing, the real part of the left side is `≥ 2^{#Ỹ} − P · 2^{#Ỹ}/(2P) > 0`, so some
  `Z ⊆ Ỹ` has `H(Z) − x ∈ ℤ`; since `0 ≤ H(Z) < 2x + 1/(M+1)` and `0 < x ≤ 1/8`, in fact
  `H(Z) = x`.

## 3. Assembly (`Croot/Main.lean`)

Given `ε > 0`, put `η = min(1, ε/(2e))` and take `c` from Proposition 2 and `D` from
Proposition 1 with `ε' = c/2`. With `x = 1 − H((N, M] \ D) = 1 − H((N, M]) + H(D)`:
`x ≤ H(D) ≤ c`, `x ≥ 1/(20 log N) − 1/M ≥ M^{−1/21}`, and the denominator of `x` divides that
of `H((N,M] \ D)`, which is `⌊N^{1/12}⌋`- hence `⌊M^{1/5}⌋`-pp-smooth. Proposition 2 gives
`Y ⊆ (M, (1+η)M]` with `H(Y) = x`, and `X = ((N, M] \ D) ∪ Y ⊆ (N, (e+ε)N]` has `H(X) = 1`
(`croot_upper`).

**Lower bound** (`croot_lower`): `X ⊆ (N, U]`, `H(X) = 1` give `1 ≤ H((N, U]) ≤ log(U/N)`.

**Consequences.** `tendsto_shortestEnd` (`U_min(N)/N → e`), and the Erdős–Graham answers:
`erdos_graham_q1` (infinitely many representations with bounded `x_k/x₁`) and
`liminf_ratio_eq_exp_one` (`liminf x_k/x₁ = e`; the lower bound uses
`x_k ≥ e(x₁ − 1)` from `croot_lower`, which leaves only finitely many sets with
`x_k ≤ (e − ε) x₁`).
