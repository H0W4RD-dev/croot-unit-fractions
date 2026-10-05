# Verification record

This record describes proof commit **`a8b4cac51866d7d9cf78b0ef70266feee06b3237`** (the commit
selected for submission). Later commits only add documentation such as this file. An earlier
record for commit `34c26c181bfcd39ba94d510b994b7aa2c33f3606` (identical except that it lacks
`Croot/Erdos286.lean` and the corresponding script entries) gave the same results.

Date: 2026-10-05. Platform: Windows 11, `x86_64-w64-windows-gnu`.

## Toolchain and dependencies

* Lean `4.33.1` (commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Release), Lake `5.0.0`,
  matching `lean-toolchain` = `leanprover/lean4:v4.33.1`.
* Mathlib `v4.33.1`, rev `0df444a360eaa60ab8c11dca51a86af692955474` (`lake-manifest.json`).
  Dependency `.olean`s were taken from a local package directory checked out at exactly the
  revisions pinned in `lake-manifest.json`; all project modules were compiled from source.

## Clean build of the selected commit

```
git clone <repo> && git checkout a8b4cac51866d7d9cf78b0ef70266feee06b3237
lake build
✔ Built Croot.Basic / Asymptotics / ElimAlgebra / Harmonic / Fourier / Lemma1 / Primes /
  Core / SmoothExist / SmoothDensity / Prop1 / Prop2 / Main / Erdos286
Build completed successfully (3330 jobs).      -- no errors, no warnings
```

`grep` for `sorry`, `admit`, `native_decide` and `axiom` declarations in `Croot/` and
`scripts/`: no matches.

## Axiom audit (`lake env lean scripts/Axioms.lean`)

```
'Croot.croot_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.croot_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.tendsto_shortestEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.erdos_graham_q1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.infinite_admissible_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.finite_admissible_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.liminf_ratio_eq_exp_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.erdos_286' depends on axioms: [propext, Classical.choice, Quot.sound]
'Croot.erdos_286_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Restatements (`lake env lean scripts/Statements.lean`)

```
'croot_upper_plain' depends on axioms: [propext, Classical.choice, Quot.sound]
'croot_lower_plain' depends on axioms: [propext, Classical.choice, Quot.sound]
'shortest_interval_plain' depends on axioms: [propext, Classical.choice, Quot.sound]
'erdos_graham_q1_plain' depends on axioms: [propext, Classical.choice, Quot.sound]
'erdos_graham_q2_plain' depends on axioms: [propext, Classical.choice, Quot.sound]
'erdos_286_formal_conjectures' depends on axioms: [propext, Classical.choice, Quot.sound]
'erdos_286_comparator_form' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `lean-verify` mechanical checks

The awards repository's `skills/lean-verify/scripts/audit.py` (sha256
`fb8c7e3b815d266425581a4f36d2343b1e3d7eae7a0cd8f4c51c055af65d01e0`) was run on a fresh clone of
the selected commit, with `scripts/Statements.lean` copied to the untracked harness module
`Croot/AuditBridge.lean`:

* `preflight`: `ready_for_target_checks: true`, no issues, HEAD = selected commit.
* `run` (explicit `lake build +Module`, `lake env lean` on each source, `#check`, `#print`,
  `#print axioms` for each target): `mechanical_status: standard_axioms_only`, exit code 0,
  `inputs_stable: true`, HEAD unchanged, for all fourteen targets: `Croot.croot_upper`,
  `Croot.croot_lower`, `Croot.tendsto_shortestEnd`, `Croot.erdos_graham_q1`,
  `Croot.liminf_ratio_eq_exp_one`, `Croot.infinite_admissible_ratio_le`,
  `Croot.finite_admissible_ratio_le`, `Croot.erdos_286`, `Croot.erdos_286_iff`,
  `erdos_graham_q1_plain`, `erdos_graham_q2_plain`, `shortest_interval_plain`,
  `erdos_286_formal_conjectures`, `erdos_286_comparator_form`.

## Requirement coverage

| Original requirement | Lean |
| --- | --- |
| Erdős–Graham Q1 (1980, p. 33, as quoted by Croot 2001): infinitely many sets `2 ≤ x₁ < ⋯ < x_k`, `∑ 1/xᵢ = 1`, with `x_k/x₁` bounded | `Croot.erdos_graham_q1`, `erdos_graham_q1_plain` |
| Erdős–Graham Q2: `liminf x_k/x₁` over all such sets equals `e` | `Croot.liminf_ratio_eq_exp_one`, `erdos_graham_q2_plain` (elementary form: `Croot.infinite_admissible_ratio_le`, `Croot.finite_admissible_ratio_le`) |
| JSP-000243 catalog phrasing: shortest interval `(N, U]` containing such denominators has `U ∼ eN` | `Croot.tendsto_shortestEnd`, `shortest_interval_plain`; `Croot.croot_upper`, `Croot.croot_lower` |
| erdosproblems.com #286 phrasing: for large `k`, `k` terms in an interval of width `(e − 1 + o(1))k` | `Croot.erdos_286`, `Croot.erdos_286_iff`, `erdos_286_formal_conjectures` (formal-conjectures statement verbatim), `erdos_286_comparator_form` |

## Limitations

* No independent kernel replay (e.g. `lean4checker`) or external comparator was run; checking
  relied on the Lean kernel during compilation and on `#print axioms`.
* The environment was an ordinary user account, not a sandbox.
* The mechanical checks do not judge statement correspondence; that is argued in `README.md`.
